## Load req packages
library(dplyr)
library(tidyverse)
library(lubridate)
library(ggridges)
library("stochvol")



# Prelims ---------------------------------------------------------------

## Load data & prelims
set.seed(123)
#options(prompt = 'R> ', continue = '+  ')

FRED = read.csv("FRED2.csv")
FRED = FRED[-1,] # Drop data trans

## Subset req cols
FRED2 = select(FRED, OILPRICEx, sasdate)
FRED2 = FRED2[complete.cases(FRED2), ]

## Transform datetime
FRED2 = FRED2 %>% 
  mutate(sasdate = mdy(sasdate))

rownames(FRED2) = FRED2$sasdate


## Add log returns to dataframe
ret = logret(FRED2$OILPRICEx, demean = TRUE)
FRED2 = FRED2[-1,]
FRED2$Ret = ret


## First plot
par(mfrow = c(2, 1), mar = c(1.9, 1.9, 1.9, .5), mgp = c(2, .6, 0))
plot(FRED2$sasdate, FRED2$OILPRICEx, type = 'l', main = "Crude-Oil price")
plot(FRED2$sasdate, ret, type = 'l', main = "Demeaned log price")


co_dev = FRED2 %>% 
  ggplot() +
  geom_line(aes(x = sasdate, y = OILPRICEx), show.legend = FALSE) +
  theme_minimal() +
  labs(title = "Crude oil price development", y = "In USD", x = NULL) +
  scale_x_date(date_breaks = "5 year", date_labels = "%y") +
  scale_y_continuous(labels = scales::comma) 


log_returns = FRED2 %>% 
  ggplot() +
  geom_line(aes(x = sasdate, y = ret, col = "#69b3a2"), show.legend = FALSE) +
  theme_minimal() +
  labs(title = "Demeaned logarithmic returns", y = "Log scale", x = NULL) +
  scale_x_date(date_breaks = "5 year", date_labels = "%y") +
  scale_y_continuous(labels = scales::comma) 


plot_lst = vector("list", length = 2)
plot_lst[[1]] = co_dev
plot_lst[[2]] = log_returns

cowplot::plot_grid(plotlist = plot_lst, nrow = 2)




# State Space Model ---------------------------------------------------------------

ck1994 = function(y,Z,Ht,Q,m,p,t,B0,V0){
  # Carter and Kohn (1994), On Gibbs sampling for state space models.
  ## Kalman Filter
  bp = B0 #the prediction at time t=0 is the initial state
  Vp = V0 #Same for the variance
  bt = matrix(0,t,m) #Create vector that stores bt conditional on information up to time t
  Vt = matrix(0,m^2,t) #Same for variances
  for (i in 1:t){
    R = Ht[i] # Messfehlervarianz #CHK LATER NOISE INNOVATION VARIANCE TO MEASUREMENT ERRORS
    Qt = Q[i] # Varianz des latenten Prozess
    H = Z[i] # Designmatrix
    
    #Prediction steps: 1. Prognosefehler berechnen, 2. Varianz d. Prognosefehlers berechnen
    cfe = y[i] - H%*%bp   # conditional forecast error
    f = H%*%Vp%*%t(H) + R    # variance of the conditional forecast error
    
    #Updating steps
    inv_f = t(H)%*%solve(f)
    
    btt = bp + Vp%*%inv_f%*%cfe  #updated mean estimate for btt Vp * inv_F is the Kalman gain
    Vtt = Vp - Vp%*%inv_f%*%H%*%Vp #updated variance estimate for btt (Kalman gain für Varianz)
    if (i < t){
      bp = btt # prediction of tau(t+1)|info up to time t = tau(t)|info up to time t
      Vp = Vtt + Qt
    }
    bt[i,] = t(btt)
    Vt[,i] = matrix(Vtt,m^2,1)
  }
  
  ### Backwards sampling
  # draw the final value of the latent states using the moments obtained from the KF filters' terminal state
  bdraw = matrix(0,t,m)
  bdraw[t,] = btt+t(chol(Vtt))%*%rnorm(nrow(Vtt))
  
  #Simulation der posterior Verteilung von den latenten Pfaden
  #Now do the backward recurssions
  for (i in 1:(t-1)){
    Qt = Q[t-i]
    bf = t(bdraw[t-i+1,])
    btt = t(bt[t-i,])
    Vtt = matrix(Vt[,t-i,drop=FALSE],m,m)
    f = Vtt + Qt
    
    inv_f = Vtt%*%solve(f)
    cfe = bf - btt
    
    bmean = t(btt) + inv_f%*%t(cfe)
    bvar = Vtt - inv_f%*%Vtt
    
    bdraw[t-i,] = bmean+t(chol(bvar))%*%rnorm(nrow(bvar))
  }
  
  return(bdraw)
}

# Declare Y
y = FRED2$OILPRICEx
#The model we are going to estimate is the unobserved components stochastic volatility model of stock and watson 2007
#                   pi(t) = tau(t) + epsilon(t)
#                   tau(t)=tau(t-1)+v(t)
#                   epsilon(t) ~ N(0, e^h(t))
#                   v(t) ~ N(0, e^s(t))

#Some MCMC preliminaries used for estimation
nsave = 90
nburn = 90
ntot = nsave+nburn


## Prior auf den initial State: Initialisierung des Kalman Filters
## der erste Wert für x_t kommt aus ner normalverteilung zentriert auf 0 mit varianz von 10000 (sehr uninformativ)
#Specifies some priors
b0 = 0 #initial state equals zero
Vb = 10000 #variance on initial state equals ten, quite uninformative


#Get some key dimensions of the data
n = length(y) #we need to substract 1 below because we lose one observation when we calculate f(t) -f(t-1)


## Storage objekte
#Before we start the Gibbs loop, we need to create storage matrices to store the MCMC output
f_store = matrix(NA,nsave,n) #stores the latent factors (taus)
h_store = matrix(NA,nsave,n) #stores the log-volatilities of the measurement errors 
s_store = matrix(NA,nsave,n) #stores the log-volatilities of the errors to the states (aus der state equation)
y_store = matrix(NA, nsave, n) #stores the predicted value of inflation


#Initialize  inflation equation SV part
## Mu: Mittelwert autoregressiver Prozess
## Phi: AR1 Parameter
## Sigma: Fehlervarianz
sv.pi.draw = list(mu = 0, phi = 0.9, sigma = 0.1, nu = Inf, rho = 0, beta = NA, latent0 = 0)
sv.pi.latent = rep(0, n)


#Sets priors for measurement error variance
B = 1
prior.pi = specify_priors(
  mu = sv_normal(mean = 0, sd = 10),
  phi = sv_beta(shape1 = 25, shape2 = 1.5),
  sigma2 = sv_gamma(shape = 0.5, rate = 1/(2*B)), #G(1/2, 1/(2*B)) \equiv  +/- sigma ~ N(0, B)
  nu = sv_infinity(),
  rho = sv_constant(0),
  latent0_variance = "stationary",
  beta = sv_multinormal(mean = 0, sd = 10000, dim = 1)
)


#Sets priors for state innovation error variances
## Für state equation -> Stochastischer trend
sv.tau.draw = list(mu = 0, phi = 0.9, sigma = 0.1, nu = Inf, rho = 0, beta = NA, latent0 = 0)
sv.tau.latent = rep(0, n)


#Sets priors for measurement error variance
C = 1 # bestimmt wie groß die Varianzen in den Volatilitätsgleichungen sein können
prior.tau = specify_priors(
  mu = sv_normal(mean = 0, sd = 10^2),
  phi = sv_beta(shape1 = 25, shape2 =  1.5),
  sigma2 = sv_gamma(shape = 0.5, rate = 1/(2*C)),
  nu = sv_infinity(),
  rho = sv_constant(0),
  latent0_variance = "stationary",
  beta = sv_multinormal(mean = 0, sd = 10000, dim = 1)
)

#Now we start the big MCMC loop
for (irep in 1:ntot){
  #Step I: Draw the latent non-stationary component using the CK/FS 1994 algorithm
  # y: Variable of Interest
  # Z: Designmatrix (n dimensionaler Vektor mit 1)
  # Ht: Fehlervarianz measurement equation
  # Q: Fehlervarianz state equation
  # m,p,t = Gleichungen, Kovariaten, Beobachtungen
  # B0, V0 = Initialisierungsparameter
  f.draw = ck1994(y = y, Z = matrix(1,n,1), Ht = exp(sv.pi.latent), Q = exp(sv.tau.latent),m=1,p = 1,t=n,B0 = b0,V0 = Vb)
  
  #Step II: Draw log-volatilities and coefficients associated with the state EQ of the volas in the measurement equation
  u.draw = y-f.draw
  h_parm = svsample_fast_cpp(u.draw,startpara=sv.pi.draw, startlatent=sv.pi.latent, priorspec = prior.pi)
  
  sv.pi.draw[c("mu", "phi", "sigma")] = as.list(h_parm$para[, c("mu", "phi", "sigma")])
  sv.pi.latent = h_parm$latent
  
  #Step III: Draw log-volatilities and coeffs in the state equation
  e.draw = f.draw[2:n,1]-f.draw[1:(n-1),1]
  e.draw = c(e.draw[1],e.draw) #DIRTY HACK, assumes that in the initial state the error equals the error in the second point in time
  
  s_parm =   svsample_fast_cpp(e.draw,startpara=sv.tau.draw, startlatent=sv.tau.latent, priorspec = prior.tau)
  sv.tau.draw[c("mu", "phi", "sigma")] = as.list(s_parm$para[, c("mu", "phi", "sigma")])
  sv.tau.latent = s_parm$latent
  
  if (irep>nburn){ #If irep exceeds the amounts of burn-ins needed, we start to store our draws
    f_store[irep-nburn,] = f.draw
    h_store[irep-nburn,] = t(sv.pi.latent)
    s_store[irep-nburn,] = t(sv.tau.latent)
    y_store[irep-nburn,] = f.draw + rnorm(n, 0, exp(.5*t(sv.pi.latent)))
  }
  print(irep) 
}



#################
#### Results ####
#################

### Posterior Verteilung des latenten Pfads
f.mean = apply(f_store,2,mean)
f.low = apply(f_store,2,quantile,0.16)
f.high = apply(f_store,2,quantile,0.84)

### Posterior Verteilung der predicted Values
y.mean = apply(y_store, 2, mean)
y.low = apply(y_store, 2, quantile, 0.16)
y.high = apply(y_store, 2, quantile, 0.84)

### Varianzen
s.mean = apply(exp(.5*s_store),2,mean)
s.low = apply(exp(.5*s_store),2,quantile,0.16)
s.high = apply(exp(.5*s_store),2,quantile,0.84)

### Messfehler
h.mean = apply(exp(.5*h_store),2,mean)
h.low = apply(exp(.5*h_store),2,quantile,0.16)
h.high = apply(exp(.5*h_store),2,quantile,0.84)


######################
#### Custom plots ####
######################

I1 = as.data.frame(cbind(y.mean, y.low, y.high, y))
I1$date = FRED2$sasdate
p1 = ggplot(I1, aes(x = date)) +
  geom_line(aes(y = y.mean, color = "y.mean")) +
  geom_line(aes(y = y.low, color = "y.low"), linetype = "dashed", alpha = 0.5) +
  geom_line(aes(y = y.high, color = "y.high"), linetype = "dashed", alpha = 0.5) +
  geom_line(aes(y = FRED2$OILPRICEx, color = "Real Y"), alpha = 0.7) +
  labs(
    title = "Posterior distribution of fitted values versus outcome",
    x = NULL,
    y = NULL,
    color='Legend'
  ) +
  scale_color_manual(values = c("lightgrey", "firebrick", "firebrick", "firebrick")) +
  theme_minimal() +
  theme(
    legend.position = c(0.05, 0.6),
    legend.background = element_rect(linetype = "solid")
  ) +
  theme(legend.key.height= unit(0.05, 'cm'),
        legend.key.width= unit(0.2, 'cm'))


I2 = as.data.frame(cbind(f.mean, f.low, f.high, y))
I2$date = FRED2$sasdate
p2 = ggplot(I2, aes (x = date)) +
  geom_line(aes(y = f.mean, color = "f.mean")) +
  geom_line(aes(y = f.low, color = "f.low"), linetype = "dashed", alpha = 0.5) +
  geom_line(aes(y = f.high, color = "f.high"), linetype = "dashed", alpha = 0.5) +
  geom_line(aes(y = FRED2$OILPRICEx, color = "Real Y"), alpha = 0.7) +
  geom_hline(yintercept = mean(y), color = "black") +
  labs(
    title = "Posterior distribution of latent trend component",
    x = NULL,
    y = NULL,
    color='Legend'
  ) +
  scale_color_manual(values = c("firebrick", "firebrick", "firebrick", "lightgrey")) +
  theme_minimal() +
  theme(
    legend.position = c(0.05, 0.6),
    legend.background = element_rect(linetype = "solid")
  ) +
  theme(legend.key.height= unit(0.05, 'cm'),
        legend.key.width= unit(0.2, 'cm'))


I3 = as.data.frame(cbind(s.mean, s.low, s.high))
I3$date = FRED2$sasdate
p3 = ggplot(I3, aes(x = date)) +
  geom_line(aes(y = s.mean, color = "s.mean")) +
  geom_line(aes(y = s.low, color = "s.low"), linetype = "dashed", alpha = 0.5) +
  geom_line(aes(y = s.high, color = "s.high"), linetype = "dashed", alpha = 0.5) +
  labs(
    title = "SD of shocks to the trend component",
    x = NULL,
    y = NULL,
    color='Legend'
  ) +
  scale_color_manual(values = c("firebrick", "firebrick", "firebrick")) +
  theme_minimal() +
  theme(
    legend.position = c(0.05, 0.6),
    legend.background = element_rect(linetype = "solid")
  ) +
  theme(legend.key.height= unit(0.05, 'cm'),
        legend.key.width= unit(0.2, 'cm'))


I4 = as.data.frame(cbind(h.mean,h.low,h.high))
I4$date = FRED2$sasdate
p4 = ggplot(I1, aes(x = date)) +
  geom_line(aes(y = h.mean, color = "h.mean")) +
  geom_line(aes(y = h.low, color = "h.low"), linetype = "dashed", alpha = 0.5) +
  geom_line(aes(y = h.high, color = "h.high"), linetype = "dashed", alpha = 0.5) +
  labs(
    title = "SD of shocks to the transitory component",
    x = NULL,
    y = NULL,
    color='Legend'
  ) +
  scale_color_manual(values = c("firebrick", "firebrick", "firebrick")) +
  theme_minimal() +
  theme(
    legend.position = c(0.05, 0.6),
    legend.background = element_rect(linetype = "solid")
  ) +
  theme(legend.key.height= unit(0.05, 'cm'),
        legend.key.width= unit(0.2, 'cm'))


plot_lst = vector("list", length = 4)
plot_lst[[1]] = p1
plot_lst[[2]] = p2
plot_lst[[3]] = p3
plot_lst[[4]] = p4

# Display plots
cowplot::plot_grid(plotlist = plot_lst, nrow = 4)