
## R version 4.0.5 ##

## Required libraries ##
library(MASS)
library(kedd)
library(mvtnorm)
library(Matrix)
library(truncnorm)
library(npmlda)
library(stats)
library(EnvStats)
library(lattice)
library(bbemkr)
library(pracma)
library(VGAM)

## Chapter 4 ##

## Asymptotic Power Study of 6 test statistics under nonparametric regression ##

## Missing Completely at Random (MAR) & ILLS method of estimation of m(X) ##

## Ex - 2 : X~N(0,1) and e|X=x =D= (1/10)*sqrt(1-(0.2*x)^(1/4))*T_x with T_x~t_{2/(0.2*x)^(1/4)} ##

## Under null hypothesis H0 ##

n = 100  ## sample size ##

B = 1000  ## number of replications ##

n1= 5 ## number of finite samples to approximate the weighted sum of chi-squares random variables ##

gm = seq(0,10,1) ## values of the mixing parameter gamma ##

pr = 0.05 ## proportion of missingness of Y-observations to be considered ##

n.hat = n*pr ## number of missing Y-values ##

alpha = 0.05 ## level of significance of test ##

e = rnorm(n, mean = 0, sd = 1)  ## generation of 100 i.i.d. errors under H0 ##

x = rtruncnorm(n,0,5,0,1)  ## generation of 100 i,i.d. covariate values under H0 ##

mx = 0.5*x^2 - x^3  ## regression function ##

y = mx + e  ## generation of responses under H0 ##

y.fix = y ## fixed original n observations on Y ##

h = 0.9 * sd(x) * (n^(-1/5))  ## bandwidth for estimation of regression function ##

## Now, n.hat number of observations on Y are to be made missing through MAR technique ##

m.hat <- function(x, y, gridpoint)  ## Definition of NW estimator based on Epanechnikov kernel ##
{
  ker = function(u) 0.75*(1-u^2) ## kernel = Epanechnikov ##
  n = length(y)
  mh = vector(,length(gridpoint))
  for(j in 1:length(gridpoint))
  {
    suma = sumb = vector(,n)
    for(i in 1:n)
    {
      suma[i] = ker((gridpoint[j] - x[i])/h) * y[i]
      sumb[i] = ker((gridpoint[j] - x[i])/h)
    }
    mh[j] = sum(suma)/sum(sumb)
  }
  return(list(gridpoint = gridpoint, mh = mh))
}

m.hat.x = function(x) m.hat(x,y,x)$mh 

p.hat = function(x) exp(m.hat.x(x))*(1+exp(m.hat.x(x)))^-1 ## probabilities of missingness of X values as logit function ##

round(p.hat(x),3) -> phat

prob = sample(phat,n.hat,replace = F)  ## generation of n.hat number of probabilities ##

count.1 = c() ## missing positions corresponding to the generated probabilities ##
for(i in 1:n.hat)
{
  for(j in 1:n)
  {
    if(prob[i]==phat[j])
    {
      count.1[i] = j
    }
  }
}

y.miss = c()  ## the Y-values at the count.1 digited places are defined as NA's ##
for(i in 1:n)
{
  if(i %in% count.1)
  {
    y.miss[i] = NA
  }
  else
  {
    y.miss[i] = y[i]
  }
}

y.dash = y.miss[-c(count.1)]  ## Y-observations after removal of NA values from y.incomplete ##

x.dash = x[-c(count.1)]  ## X-observations corresponding to y.dash ##

## Now, to estimate the unknown regression function using ILLS method at x.dash in first step as follows. ##

ep.kernel = function(u) 0.75*(1-u^2) ## Epanechnikov kernel ##

M1<- function(u)  
{
  vec1<- c()
  for(i in 1:length(x.dash))
  {
    vec1[i]<- (u-x.dash[i])*ep.kernel((u-x.dash[i])/h)
  }
  return(sum(vec1))
}

M2<- function(v)  
{
  vec2<- c()
  for(i in 1:length(x.dash))
  {
    vec2[i]<- (v-x.dash[i])^2*ep.kernel((v-x.dash[i])/h)
  }
  return(sum(vec2))
}

lls1<- function(c)
{
  g1 = c()
  for(i in 1:length(x.dash))  { g1[i]<- (M2(x.dash[i])-(x.dash[i]-c)*M1(x.dash[i]))*ep.kernel((x.dash[i]-c)/h)*y.dash[i]  }
  g2 = c()
  for(i in 1:length(x.dash))  { g2[i]<- (M2(x.dash[i])-(x.dash[i]-c)*M1(x.dash[i]))*ep.kernel((x.dash[i]-c)/h)  }
  return(sum(g1)/sum(g2))
}

## least square estimation of intercept based on non-missing (X,Y)-observations only ##

t0.hat<- c()  ## t0.hat is also the first step estimator of the regression function based on non-missing observations of (X,Y) ##
for(i in 1:length(x.dash))
{
  t0.hat[i]<- lls1(x.dash[i])
}

x.miss = x[count.1]  ## X-observations corresponding to missing Y-values ##

m.hat.miss = c()  ## estimation of regression function at the missing observations of Y ##
for(i in 1:length(x.miss))
{
  m.hat.miss[i] = lls1(x.miss[i])
}

m.hat.miss.arranged<- c()  
for(i in 1:length(count.1))
{
  m.hat.miss.arranged[i]<- m.hat.miss[rank(count.1)==i]
}

y.complete<- replace(y.miss,which(is.na(y.miss)==T),m.hat.miss.arranged)   ## complete data on Y after imputation ##

## Now, based on n paired observations (X, Y.complete), the regression function of the complete model needs to be estimated. ##

M1.1<- function(u)  
{
  v1<- c()
  for(i in 1:n)
  {
    v1[i]<- (u-x[i])*ep.kernel((u-x[i])/h)
  }
  return(sum(v1))
}

M2.1<- function(v)  
{
  v2<- c()
  for(i in 1:n)
  {
    v2[i]<- (v-x[i])*ep.kernel((v-x[i])/h)
  }
  return(sum(v2))
}


lls2<- function(c)
{
  r1 = c()
  for(i in 1:n)  { r1[i]<- (M2.1(x[i])-(x[i]-c)*M1.1(x[i]))*ep.kernel((x[i]-c)/h)*y.complete[i]  }
  r2 = c()
  for(i in 1:n)  { r2[i]<- (M2.1(x[i])-(x[i]-c)*M1.1(x[i]))*ep.kernel((x[i]-c)/h)  }
  return(sum(r1)/sum(r2))
}

## least square estimation of intercept based on full set of (X,Y)-observations ##

s0.hat<- c()  ## t0.hat is also the first step estimator of the regression function based on non-missing observations of (X,Y) ##
for(i in 1:n)
{
  s0.hat[i]<- lls2(x[i])
}

## s0.hat is the secind step cum final estimator of the regression function of the model ##


e.hat = y.complete - s0.hat ## estimation of errors ##

e.cen = e.hat - mean(e.hat) ## estimation of centered errors ##

e.cen.boot<- sample(e.cen, n, replace = T) ## resamples of centered errors from the empirical distribution function of centered error ##

y.boot<- s0.hat+e.cen.boot ## resampled responses ##

DATA<- cbind.data.frame(x,e.cen.boot,y.boot) ## dataset on X-observations and resampled responses ##

x.sort <- c() ## ordered X observations ##
e.sort<- c()  ## induced cenetered errors ##
y.sort<- c()  ## induced resampled responses ##
for(i in 1:n)
{
  x.sort[i]<- x[rank(x)==i]
  e.sort[i]<- e.cen.boot[which(x==x.sort[i])]
  y.sort[i]<- y.boot[which(x==x.sort[i])]
}

e3.boot<- c()  ## third difference of induced centered errors ##
for(i in 1:n)
{
  if(i==1)
  {
    e3.boot[i] = -e.sort[2]
  }
  else if(i==2)
  {
    e3.boot[i] = -2*e.sort[1]+3*e.sort[2]-e.sort[3]
  }
  else if(i==n)
  {
    e3.boot[i] = e.sort[n-2]-3*e.sort[n-1]+2*e.sort[n]
  }
  else
  {
    e3.boot[i] = e.sort[i-2]-3*e.sort[i-1]+3*e.sort[i]-e.sort[i+1]
  }
}

emp.cdf.e3.H0 = ecdf(e3.boot)(e3.boot) ## empirical cdf of third difference of induced centered errors ##

y3.boot<- c()  ## third difference of induced resampled responses ##
for(i in 1:n)
{
  if(i==1)
  {
    y3.boot[i] = -y.sort[2]
  }
  else if(i==2)
  {
    y3.boot[i] = -2*y.sort[1]+3*y.sort[2]-y.sort[3]
  }
  else if(i==n)
  {
    y3.boot[i] = y.sort[n-2]-3*y.sort[n-1]+2*y.sort[n]
  }
  else
  {
    y3.boot[i] = y.sort[i-2]-3*y.sort[i-1]+3*y.sort[i]-y.sort[i+1]
  }
}

data.xy<- cbind(x.sort,y3.boot)  ## data on ordered X-observations and third difference of induced resampled responses ##
emp.cdf.x = ecdf(x)(x.sort) ## empirical cdf of X ##
dt.x<- data.xy[,1]
dt.y<- data.xy[,2]

data.pts.x1<- unname(quantile(dt.x, probs = ((1:n1)/n1)))  ## n1(=5) marginal qunatiles based on X-observations ##
data.pts.y1<- unname(quantile(dt.y, probs = ((1:n1)/n1)))  ## n1(=5) marginal qunatiles based on induced responses ##
points.all<- cbind(data.pts.x1, data.pts.y1) ## bivariate quantiles on X and induced third order difference of Y ##

u = ecdf(dt.x)(x.sort) ## empirical CDF values of X ##
v = ecdf(dt.y)(y3.boot) ## empirical CDF values of induced Y ##

###############################################################################################################################

## Power of Kolmogorov Smirnov test statistic ##

covariance.matrix = matrix(0,n,n)  ## covariance matrix for the Gaussian process (Wiener process) Z0(u,v) ##
for(i in 1:n)
{
  for(j in 1:n)
  {
    covariance.matrix[i,j] = (min(u[i],u[j])-u[i]*u[j])*(min(v[i],v[j])-v[i]*v[j]) 
  }
}

Z0.uv<- vector("list",B)  ## generation of Wiener processes of size n in B(=1000) resamples ##
for(j in 1:B)
{
  Z0.uv[[j]]<- as.vector(rmvnorm(1,mean = rep(0,n), covariance.matrix))
}

KS.0<- c()  ## Kolmogoriv smirnov values under H0 ##
for(j in 1:B)
{
  KS.0[j] = max(abs(Z0.uv[[j]]))
}

Ks.critical = quantile(KS.0, probs = 1-alpha)  ## 5% critical value of Tn,KS ##
Ks.critical

## Under alternative hypothesis H1 ##

e.x<- c()  ## conditional error observations of size n under H1 ##
k1<- c()
k2<- c()
k3<- c()
for(i in 1:n)
{
  k1[i]<- (0.2*x.sort[i])^(1/4)
  k2[i]<- 10*sqrt(k1[i])
  k3[i]<- sqrt(1-k1[i])
  e.x[i]<- k3[i]*rt(1, round(2/k1[i],0), 0)
}

## computation of the ratio h for contiguous alternatives ## ##

h1<- c()  
y1<- c()
f1<- c()
f2<- c()
w1<- c()
w2<- c()
w4<- c()
for(i in 1:n)
{
  y1[i]<- exp(0.5*e.x[i]^2)
  f1[i]<- gamma((1+2/k1[i])/2)
  f2[i]<- (1+(2/k1[i]))/2
  w1[i]<- gamma(1/k1[i])
  w2[i]<- 1+((50*(e.x[i]^2)*k1[i])/(1-(k1[i])))
  h1[i]<- ((k2[i]*y1[i]*f1[i]*w2[i]^-f2[i])/(k3[i]*w1[i]))-1
}

power = function(t) ## Power calculation of Tn,KS ##
{
  Z1.uv<- vector("list",B) ## generation of Wiener process under H1 ##
  for(j in 1:B)
  {
    Z1.uv[[j]]<- Z0.uv[[j]]+cov(t*(h1-1),Z0.uv[[j]]/sqrt(n))
  }
  KS.1<- c()  ## generation of values of Kolmogorov Smirnov test statistics under H1 ##
  for(j in 1:B)
  {
    KS.1[j] = max(abs(Z1.uv[[j]]))
  }
  p = mean(KS.1>Ks.critical) ## proportion of KS values exceeding the 5% critical value provides the power of Tn,KS ##
  return(p)
}

Power_of_KS<- c() ## Powers of Tn,KS for different values of gamma ##
for(i in 1:length(gm))
{
  Power_of_KS[i]<- power(i-1)
}
Power_of_KS

################################################################################################################################

#### Power of Cramer von Mises test statistic ####

Z.vec<- vector("list", B)  ## generation of n1 independent N(0,1) random variables ##
for(j in 1:B)
{
  Z.vec[[j]]<- matrix(0,n1,n1)
  for(i in 1:n1)
  {
    for(k in 1:n1)
    {
      Z.vec[[j]][i,k]<- rnorm(1)
    }
  }
}

eigenvalue.CM<- matrix(0,n1,n1)  ## computation of eigenvalues associated with the kernel of Tn,CM ##
for(i in 1:n1)
{
  for(j in 1:n1)
  {
    eigenvalue.CM[i,j]<- 1/(pi^4*i^2*j^2)
  }
}

Tn.CM.null<- c() ## B values on Cramer von Mises test statistic under H0 ##
for(j in 1:B)
{
  Tn.CM.null[j]<- sum((Z.vec[[j]])^2*eigenvalue.CM)
}

CM.critical<- quantile(Tn.CM.null, probs = 1-alpha)  ## 5% critical value of Tn,CM ##
CM.critical

aij = function(i,j) {mean(h1*2*sin(pi*i*x.sort)*sin(pi*j*y3.boot))} ## calculation of the coefficients a_ij's ##

a.vals = matrix(0,n1,n1)
for(i in 1:n1)
{
  for(j in 1:n1)
  {
    a.vals[i,j]<- aij(i,j)
  }
}

power.CM = function(b)  ## power calculation of Cramer von Mises ##
{
  Tn.CM.alt<- c()  ## B values on Cramer von Mises test statistic under H1 ##
  for(p in 1:B)
  {
    Tn.CM.alt[p]<- sum(eigenvalue.CM*(Z.vec[[p]]+b*a.vals)^2)
  }
  return(mean(Tn.CM.alt>CM.critical))
}

Power_of_CM<- c()  ## Powers of Tn,CM for different values of gamma ##
for(i in 1:length(gm))
{
  Power_of_CM[i]<- power.CM(i-1)
}
Power_of_CM

#######################################################################################################################

#### Power of Anderson-Darling test statistic ####

Z.vec.star<- vector("list", B)  ## generation of n1 independent N(0,1) random variables ##
for(j in 1:B)
{
  Z.vec.star[[j]]<- matrix(0,n1,n1)
  for(i in 1:n1)
  {
    for(k in 1:n1)
    {
      Z.vec.star[[j]][i,k]<- rnorm(1)
    }
  }
}

eigenvalues.AD<- matrix(0,n1,n1)  ## computation of eigenvalues associated with the kernel of Tn,AD ##
for(i in 1:n1)
{
  for(j in 1:n1)
  {
    eigenvalues.AD[i,j]<- 1/(i*j*(i+1)*(j+1))
  }
}

Tn.AD.null<- c()  ## Powers of Tn,AD for different values of gamma ##
for(j in 1:B)
{
  Tn.AD.null[j]<- sum(eigenvalues.AD*(Z.vec.star[[j]])^2)
}

AD.critical<- quantile(Tn.AD.null, probs = 1-alpha)  ## Powers of Tn,AD for different values of gamma ##
AD.critical

## Computation of eigenfunctions ##
eigenfunction.u<- function(o)   
{
  k = 2*(2*o+1)/(o*(o+1))
  l = sqrt(k)*u*(u-1)
  if(o==1)
  {
    return(l*legendre(0,2*u-1))
  }
  else
  {
    return(l*legendre(o-1,2*u-1)[2,])
  }
}
eigenfunction.v<- function(o)
{
  k = 2*(2*o+1)/(o*(o+1))
  l = sqrt(k)*v*(v-1)
  if(o==1)
  {
    return(l*legendre(0,2*v-1))
  }
  else
  {
    return(l*legendre(o-1,2*v-1)[2,])
  }
}

aij.star = function(i,j) {mean(h1*eigenfunction.u(i)*eigenfunction.v(j))}  ## values of a*_ij's ##

a.vals.star = matrix(0,n1,n1)
for(i in 1:n1)
{
  for(j in 1:n1)
  {
    a.vals.star[i,j]<- aij.star(i,j)
  }
}

power.AD<- function(b)  ## power calculation of Anderson Darling test statistic ##
{
  Tn.AD.alt<- c()
  for(j in 1:B)
  {
    Tn.AD.alt[j]<- sum(eigenvalues.AD*(Z.vec.star[[j]]+b*a.vals.star)^2)
  }
  return(mean(Tn.AD.alt>AD.critical))
}

Power_of_AD<- c()  ## Powers of Tn,AD for different values of gamma ##
for(i in 1:length(gm))
{
  Power_of_AD[i]<- power.AD(i-1)
}
Power_of_AD

#######################################################################################################################

#### Power of Tn1 ####

e3.boot1<- c()  ## third order difference of conditional error under H1 ##
for(i in 1:n)
{
  if(i==1)
  {
    e3.boot1[i] = -e.x[2]
  }
  else if(i==2)
  {
    e3.boot1[i] = -2*e.x[1]+3*e.x[2]-e.x[3]
  }
  else if(i==n)
  {
    e3.boot1[i] = e.x[n-2]-3*e.x[n-1]+2*e.x[n]
  }
  else
  {
    e3.boot1[i] = e.x[i-2]-3*e.x[i-1]+3*e.x[i]-e.x[i+1]
  }
}

dataset1 = cbind(x.sort,e3.boot1)  ## dataset on ordered X-observations and third order difference of conditional error under H1 ##

emp.cdf.e3.H1 = ecdf(e3.boot1)(e3.boot1) ## empirical CDF of third order difference of conditional error under H1 ##

## Calculation of mean of asymptotic distribution of Tn1 under contiguous alternatives Hn ##
U = 2*emp.cdf.x*emp.cdf.e3.H0+2*(1-emp.cdf.x)*(1-emp.cdf.e3.H0)-1
V = 2*emp.cdf.x*emp.cdf.e3.H1+2*(1-emp.cdf.x)*(1-emp.cdf.e3.H1)-1
Tn1.mean = 2*gm*mean(V)

## Calculation of variance of asymptotic distribution of Tn1 under contiguous alternatives Hn ##

Tn1.variance = 4*mean(U^2)

Tn1.sd = sqrt(Tn1.variance)  ## standard deviation of Tn1 ##

Tn1.critical = qnorm(1-alpha,0,Tn1.sd)  ## 5% critical value of Tn1 ##

Power_of_T1<- round((1-pnorm((Tn1.critical-Tn1.mean)/Tn1.sd)),3)  ## Powers of Tn1 for different values of gamma ##
Power_of_T1

#######################################################################################################################

#### Power of Tn2 ####

kernel.T2<-function(a,b)  ## kernel function of Tn2 ##
{
  x<-0
  for(i in 1:(n-3))
  {
    for(j in (i+1):(n-2))
    {
      for(k in (j+1):(n-1))
      {
        for(l in (k+1):n)
        {
          x<-x+(sign(abs(a-dt.x[j])+abs(dt.x[k]-dt.x[l])-abs(a-dt.x[k])-abs(dt.x[j]-dt.x[l]))*sign(abs(b-dt.y[j])+abs(dt.y[k]-dt.y[l])-abs(b-dt.y[k])-abs(dt.y[j]-dt.y[l])))
        }
      }
    }
  }
  return(x/choose(n,4))
}

L<- matrix(0,n1,n1)  ## Matrix with elements being the values of kernel function of Tn2 approximated at the bivariate marginal quantiles of X and third order difference of Y ##
{
  for(p in 1:n1)
  {
    for(q in 1:n1)
    {
      L[p,q]<- kernel.T2(data.pts.x1[p],data.pts.y1[q])
    }
  }
}

lmat2<- (L+t(L))/2  ## Symmetrization of L as lmat2, since L and lmat2 have same eigenvalues and eigenvectors. ##

E<- eigen(lmat2) ## eigenvalue decomposition of real symmetric matrix E as E=VDV^T, where D is the diagonal matrix with diagonal entries as the eigenvalues of E and V being the matrix of eigenvectors of E ##

lambdas2<- E$values ## real eigenvalues associated with L ##

V2<- E$vector ## matrix of real eigenvectors associated with L ##

V2.t<- t(V2)  ## transpose of V2 ##

## computation of the coefficeints a_k, k=1,...,n ##
ak<- vector("list", n1)  
for(k in 1:n1)
{
  for(i in 1:n1)
  {
    ak[[k]][i]<- h1[1:n1][i]*V2[i,k]*V2.t[k,i]
  }
}
ak1<- c()  
for(k in 1:n1)
{
  ak1[k]<- mean(ak[[k]])
}

Z.val<- vector("list", B)  ## generation of B i.i.d. standard normal variates ##
for(j in 1:B)
{
  Z.val[[j]]<- rnorm(n1)
}

## Computation of B values of Tn2 under H0 ##
T2.null.vals<- vector("list", B)  
for(d in 1:B)
{
  for(k in 1:n1)
  {
    T2.null.vals[[d]][k]<- lambdas2[k]*((Z.val[[d]][k])^2-1)
  }
}
T20<- c()  ## B values of Tn2 under H0 ##
for(d in 1:B)
{
  T20[d]<- sum(T2.null.vals[[d]])
}

T2.quantile<- quantile(T20, probs = 1-alpha)  ## 5% critical value of Tn2 ##

T2.alt.vals<- vector("list", length(gm))  ## Computation of B values of Tn2 under H1 ##
for(m in 1:length(gm))
{
  for(d in 1:B)
  {
    T2.alt.vals[[m]][d]<- sum(lambdas2*((Z.val[[d]]+gm[m]*ak1)^2-1))
  }
}

Power_of_T2<- c()   ## Power values of Tn2 for different values of gamma ##
for(i in 1:length(gm))
{
  Power_of_T2[i]<- mean(T2.alt.vals[[i]]>T2.quantile)  
}
Power_of_T2

#######################################################################################################################

#### Power of Tn3 ####

kernel.T3<-function(a,b)  ## kernel function of Tn3 ##
{
  x<-0
  for(i in 1:(n-3))
  {
    for(j in (i+1):(n-2))
    {
      for(k in (j+1):(n-1))
      {
        for(l in (k+1):n)
        {
          x<-x+(1/4)*((abs(a-dt.x[j])+abs(dt.x[k]-dt.x[l])-abs(a-dt.x[k])-abs(dt.x[j]-dt.x[l]))*(abs(b-dt.y[j])+abs(dt.y[k]-dt.y[l])-abs(b-dt.y[k])-abs(dt.y[j]-dt.y[l])))
        }
      }
    }
  }
  return(x/choose(n,4))
}

L1<- matrix(0,n1,n1)  ## Matrix with elements being the values of kernel function of Tn3 approximated at the bivariate marginal quantiles of X and third order difference of Y ##
{
  for(p in 1:n1)
  {
    for(q in 1:n1)
    {
      L1[p,q]<- kernel.T3(data.pts.x1[p],data.pts.y1[q])
    }
  }
}

lmat3<- (L1+t(L1))/2  ## Symmeytrization of L1 as lmat3, since L1 and lmat3 have same eigenvalues and eigenvectors. ##

E1<- eigen(lmat3) ## eigenvalue decomposition of real symmetric matrix E1 ##

lambdas3<- E1$values ## real eigenvalues of lmat3 ##

V3<- E1$vector ## real eigenvectors of lmat3 ##

V3.t<- t(V3) ## transpose of V3 ##

## computation of the coefficeints a.star_k, k=1,...,n ##
a.star.k<- vector("list", n1)
for(k in 1:n1)
{
  for(i in 1:n1)
  {
    a.star.k[[k]][i]<- h1[1:n1][i]*V3[i,k]*V3.t[k,i]
  }
}
a.star.k1<- c()
for(k in 1:n1)
{
  a.star.k1[k]<- mean(a.star.k[[k]])
}

## Generation of B i.i.d. standard normal variates ##
Z.val<- vector("list", B)
for(j in 1:B)
{
  Z.val[[j]]<- rnorm(n1)
}

## Computation of B values of Tn3 under H0 ##
T3.null.vals<- vector("list", B)
for(d in 1:B)
{
  for(k in 1:n1)
  {
    T3.null.vals[[d]][k]<- lambdas3[k]*((Z.val[[d]][k])^2-1)
  }
}
T30<- c()
for(d in 1:B)
{
  T30[d]<- sum(T3.null.vals[[d]])
}

T3.quantile<- quantile(T30, probs = 1-alpha)  ## 5% critical value of Tn3 ##

## Computation of values of Tn3 under Hn ##
T3.alt.vals<- vector("list", length(gm))  
for(m in 1:length(gm))
{
  for(d in 1:B)
  {
    T3.alt.vals[[m]][d]<- sum(lambdas3*((Z.val[[d]]+gm[m]*a.star.k1)^2-1))
  }
}

Power_of_T3<- c()  ## Powers of Tn,3 for different values of gamma ##
for(i in 1:length(gm))
{
  Power_of_T3[i]<- mean(T3.alt.vals[[i]]>T3.quantile)
}

Power_table = cbind(gm,Power_of_KS,Power_of_CM,Power_of_AD,Power_of_T1,Power_of_T2,Power_of_T3)
Power_table

## graphical representation of the power curves of T1, T2 and T3 ##

KS = Power_of_KS
CM = Power_of_CM
AD = Power_of_AD
T1 = Power_of_T1
T2 = Power_of_T2
T3 = Power_of_T3

plot(gm, KS, xlim=c(0,10), ylim=c(0,1), type="l", pch=10, col="red", xlab=expression(gamma), ylab=expression("Nonparametric Powers (MAR & ILLS)"))
# Add a line
lines(gm, CM, xlim=c(0,10), ylim=c(0,1), pch=10, col="purple", type="l")
# Add a line
lines(gm, AD, xlim=c(0,10), ylim=c(0,1), pch=10, col="violet", type="l")
# Add a line
lines(gm, T1, xlim=c(0,10), ylim=c(0,1), pch=10, col="black", type="l")
# Add a line
lines(gm, T2, xlim=c(0,10), ylim=c(0,1), pch=10, col="green", type="l")
# Add a line
lines(gm, T3, xlim=c(0,10), ylim=c(0,1), pch=10, col="blue", type="l")
# Add a legend
legend("topleft",
       c(expression(paste('T'['n,KS']),paste('T'['n,CM']),paste('T'['n,AD']),paste('T'['n,1']),paste('T'['n,2']),paste('T'['n,3']))),
       fill=c("red","purple","violet","black","green","blue"))

