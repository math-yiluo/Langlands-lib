# Real torus theta identity at determinant scale

`ArchimedeanDeterminantThetaStatement` packages a theta identity on the
coordinate torus with a **single** scale, and a meromorphic continuation and
functional equation for the corresponding Schwartz torus zeta integrals.
This is an internal step toward the principal-series coefficient integrals
in Task 7400; no matrix coefficient or Whittaker integral is identified here.

Let $n=m+1$, with coordinates indexed by `Fin (m+1)`, and choose parities
$e_i\in\{0,1\}$ and complex parameters $u_i$. Off the coordinate
hyperplanes set

\[
 \delta(x)=\prod_i |x_i|,\qquad
 G_{e,u,F}(x)=F(x)\prod_i\operatorname{sgn}(x_i)^{e_i}|x_i|^{u_i-1}.
\]

The Lean `detScale` uses `absPos` (value $1$ at $0$) for each absolute
value, and `weightedKernel` sets the density to zero if any coordinate
vanishes. Integrals are with respect to coordinate Lebesgue measure. Write
$F^\vee=\texttt{fourierInvN}\,F$ for the positive-sign Fourier integral,
with phase $\exp(2\pi i\sum_i x_i y_i)$.

## Determinant theta identity

`detH` and `detK` are the multiplicative convolutions of the respective
`pairH` and `pairK` of `ArchimedeanTateTheta` over all $n$ characters.
Call them $H,K$. For $F$ integrable, assume there are real exponents
$M,M_d$ with $|G_{e,u,F}|\delta^M$ and
$|G_{e,-u,F^\vee}|\delta^{M_d}$ integrable (the exponents are supplied
explicitly in Lean). Then for every $a>0$,

\[
 \int G_{e,u,F}(x)H(a\delta(x))\,dx
  =a\int G_{e,-u,F^\vee}(y)K(a^{-1}\delta(y))\,dy.
\]

Apply `theta_mconv` from `ArchimedeanMellinConvolution` to the left,
expanding it into an integral over independent positive scales of
product $a$. The torus theta identity `torus_theta_identity` multiplies
by $a$ and inverts these scales. Their inverse scales have product
$a^{-1}$ and are parametrized by the opposite log-coordinate slope.
Apply `theta_mconv` in this orientation on the dual side and then
`mconv_neg` to recover the convolution $K$. Each invocation of Fubini
uses only the respective fixed integrable weight.

## Continuation on the torus

Let $Z(s)=\int G_{e,u,F}(x)\delta(x)^s\,dx$ (`torusZeta`) and let $Z_d$
use $-u,F^\vee$ instead. Put

\[
 L(s)=\prod_i\Gamma_{\mathbb R}(s+u_i+e_i),\quad
 L_d(s)=\prod_i\Gamma_{\mathbb R}(s-u_i+e_i),\quad
 E=\prod_i i^{e_i}.
\]

For Schwartz $F$ there are functions $A,A_d:\mathbb C\to\mathbb C$
meromorphic on all of $\mathbb C$, agreeing with $Z,Z_d$ on a common
right half-plane. In the codiscrete filter of $\mathbb C$ they satisfy

\[
 L(s)A_d(1-s)=E\,L_d(1-s)A(s).
\]

The auxiliary `torus_continuation` gives this if the weighted-norm
integrals of both kernels exist for every real exponent above a common
threshold and $F$ is integrable. The Mellin product formula gives
$\operatorname{mellin}(H)(-s)=E\exp(ns^2)L(s)^{-1}$ and
$\operatorname{mellin}(K)(s-1)=\exp(ns^2)L_d(1-s)^{-1}$, with totalized
inverses. The Mellin transforms evaluated at $-s$ are both nonzero
sufficiently far to the right by the gamma nonvanishing in positive
real part. Analyticity and nonvanishing at one point give the needed
cancellation off discrete sets. `determinant_pair_continuation` packages
this application of `ArchimedeanMellinPair.exists_continuation` for any two
measured kernels with positive scales, the required weighted-norm
integrability, and the theta identity for this specific convolved pair.
`torus_continuation` supplies those premises on the coordinate space.

For the Schwartz specialization, `schwartzFourierInvN_apply` identifies
the transform with the transported Euclidean Schwartz inverse Fourier
transform, using the volume-preserving coordinate equivalence. In
`integrable_weightedKernel_schwartz`, when every shifted real exponent
is nonnegative, the norm of the combined character and determinant
weight is bounded by a polynomial in $\max(1,\|x\|)$. The needed
weighted-norm integrability for each exponent on a right half-plane
follows from Schwartz integrability with polynomial weights, on both
sides. This supplies the hypotheses of `torus_continuation`.

## Source and scope

Hervé Jacquet, *Archimedean Rankin–Selberg integrals* (2009),
`jacquet-2009-archimedean-rankin-selberg`, §4.2 (pp. 22–23) for the
pairs and scaling, §4.3, Proposition 4.1 (pp. 23–25) for continuation
from a theta identity, §4.4, proof of Proposition 4.3 (p. 28) for the
convolution step, and §4.6 (pp. 29–30) for the Tate factors. The result
uses the finite real-character product and a single explicit convolved
pair; it does not claim the general converse, holomorphic normalized
multiples, or vertical-strip bounds. It supplies the determinant-scale
analytic calculation for a later upper-triangular marginal of a square
matrix Schwartz test in §4.7 (pp. 30–31).
