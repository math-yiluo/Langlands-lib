# Real Tate theta identities

`Langlands.Global.RankinSelbergGlobal.ArchimedeanTateThetaStatement` is an
internal analytic step toward the real-place functional equation
`RealPlaceFunctionalEquationStatement`. It packages the real Tate theta
identity `ArchimedeanTateTheta.theta_identity` and its finite product with
independent positive scales (`torus_theta_identity`). Both use Lebesgue
measure and the **positive** Fourier sign, i.e. Mathlib's inverse Fourier sign.
The additive character is $x\mapsto \exp(2\pi i x)$.

## Kernels and statement

For parity $e\in\{0,1\}$ and $u\in\mathbb C$, write $\chi_{e,u}(x)=
\operatorname{sgn}(x)^e |x|^u$ for $x\ne 0$. The functions
$h=\texttt{pairH}\ e\ u$ and $k=\texttt{pairK}\ e\ u$ are the inverse Mellin
transforms on the line $\operatorname{Re} w=0$ of

\[
 m_h(w)=i^e\frac{\exp(w^2)}{\Gamma_{\mathbb R}(-w+u+e)},\qquad
 m_k(w)=\frac{\exp((w+1)^2)}{\Gamma_{\mathbb R}(-w-u+e)}.
\]

Thus at $w=-s$ and $w=s-1$, respectively, the two functions use the same
Gaussian $\exp(s^2)$, with the factor $i^e$ on the first side. The module
proves that $h,k$ are measurable, rapidly decreasing in the sense of
`ArchimedeanMellinPair.RapidDecay` (for every real $M$ there is $C$ bounding
$|h(t)|$ or $|k(t)|$ by $Ct^M$ for $t>0$), continuous at each $t>0$, and have
the indicated Mellin transforms. Here and below the displayed reciprocals
are the totalized Lean inverses.

For $a>0$ and $f$ Schwartz on $\mathbb R$, the first assertion is

\[
 \int_{\mathbb R^\times} f(x)\chi_{e,u}(x) h(a|x|)\frac{dx}{|x|}
 = a\int_{\mathbb R^\times} \mathcal F^{-1} f(y)\chi_{e,-u}(y)
          k(a^{-1}|y|)\frac{dy}{|y|}.
\]

Lean integrates on all of $\mathbb R$ with the Tate `integrand` set to zero
at the origin and `absPos` equal to $|x|$ except for the value $1$ at $0$.
Define $H_a(x)=\chi_{e,u}(x)|x|^{-1}h(a|x|)$ and
$K_b(y)=\chi_{e,-u}(y)|y|^{-1}k(b|y|)$ off zero and set both to zero at zero.
These are `kernelH` and `kernelK`. The second assertion is that for every
$n$ (including $0$), every list $(e_i,u_i,a_i)$ indexed by `Fin n` with
$a_i>0$, and every integrable $F:\mathbb R^n\to\mathbb C$,

\[
 \int F(x)\prod_i H_{a_i}^{(e_i,u_i)}(x_i)\,dx
   = \Bigl(\prod_i a_i\Bigr)\int
         \texttt{fourierInvN}(F)(y)\prod_i K_{a_i^{-1}}^{(e_i,u_i)}(y_i)\,dy .
\]

`fourierInvN` is the inverse Fourier integral with kernel
$\exp(2\pi i\sum_i x_i y_i)$, not a hypothesis that the transform is Schwartz
or integrable.

## Lean proof

Entire reciprocal gamma factors have exponential-type bounds on vertical
strips (`ArchimedeanGammaBounds`); multiplication by the Gaussian gives
strip decay for the Mellin-side functions. `ArchimedeanInverseMellin` then
gives measurability, rapid decay, and the Mellin transform formulas.

The two theta functions of $a$ have the same Mellin transform on the single
line $\operatorname{Re} w=\operatorname{Re} u-1/2$. The Mellin transform of
the first is the real Tate zeta integral at $u-w$ times $m_h(w)$; that of
the second is the dual Tate zeta integral at $1-(u-w)$ times $m_k(-w-1)$.
The Tate functional equation from `RealTateProof` applies on this line,
where the shifted Tate parameter has real part $1/2$. The zeta integrals
are bounded along that line by their absolute-value integrals, which,
together with the pair's decay, gives integrability of the two Mellin
transforms there. Mellin inversion, with dominated convergence for
continuity of the theta functions at positive $a$, gives the first identity.

The kernels are integrable by their rapid-decay estimates at zero and
infinity. Fubini for the positive-sign Fourier kernel and the identity
against Schwartz tests show that $H_a=a\,\mathcal F^{-1}K_{a^{-1}}$ almost
everywhere (`kernelH_ae_eq`), using compactly supported smooth tests to
identify locally integrable functions. Pull back the coordinatewise
almost-everywhere identities to the product measure and combine the
Fourier integrals by Fubini; their product kernel is the dot-product Fourier
kernel defining `fourierInvN`. The resulting identity only needs $F$ to be
integrable.

## Source and scope

Hervé Jacquet, *Archimedean Rankin–Selberg integrals* (2009),
`jacquet-2009-archimedean-rankin-selberg`, §4.2 (pp. 22–23) for the
pair and its scaling, Proposition 4.2 (pp. 26–28) for the theta formulation,
and §4.6, (4.2) (pp. 29–30) for the Tate example. The first assertion is the
real Tate specialization for one explicit pair and the indicated Fourier
convention. The proof uses a common line of absolute convergence instead
of the general converse proposition with its strip hypotheses. The finite
product with independent scales is derived from this specialization. It
is a step toward the convolution method of §4.4 (p. 28) and the
principal-series coefficient integrals of §4.7 (pp. 30–31); it does not
assert the general converse, the matrix coefficient identity, or the
real-place Rankin–Selberg functional equation.
