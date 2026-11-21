# Mellin convolution in logarithmic coordinates

This is an internal analytic step toward the real principal-series coefficient
integrals in Task 7400. `ArchimedeanMellinConvolutionStatement` packages two
facts: closure under multiplicative convolution with a product formula for the
Mellin transform, and a Fubini identity on a general measure space with a
product of positive weights.

## Convolution and Mellin transform

For $m\ge 0$, a list $h_0,\ldots,h_m:\mathbb R\to\mathbb C$, and a real
parameter $\varepsilon$, put

\[
 H_\varepsilon(t)=\int_{\mathbb R^m}
 h_0\bigl(t\exp(-\varepsilon\textstyle\sum_{j=1}^m\tau_j)\bigr)
 \prod_{j=1}^m h_j\bigl(\exp(\varepsilon\tau_j)\bigr)\,d\tau .
\]

This is `mconv ε (h 0) (fun j => h j.succ)`, with $\mathbb R^m$ indexed by
`Fin m` and the list by `Fin (m+1)`. When $\varepsilon=1$ it is the
multiplicative convolution on the positive real line with logarithmic
Lebesgue measure (equivalently $dt/t$ in each multiplicative variable).
The first part of the statement asserts that if all $h_j$ are measurable
and rapidly decreasing in `ArchimedeanMellinPair.RapidDecay` (each real
power $t^M$ bounds the norm up to a constant for $t>0$), then $H_1$ is
measurable and rapidly decreasing and Mathlib's Mellin transforms satisfy

\[
 \operatorname{mellin}(H_1)(s)=\prod_{i=0}^m\operatorname{mellin}(h_i)(s)
 \qquad(s\in\mathbb C).
\]

The proof bounds each $e^{p\tau}|h_j(e^{\varepsilon\tau})|$ by a constant
times $e^{-|\tau|}$ using two real-power bounds when $\varepsilon\ne0$.
A real-power bound on $h_0$ then bounds the convolution integrand by
$Ct^M$ times a product of integrable one-variable functions. This gives
integrable fibers and the bound on the integral of the absolute value for
every $M$. For the Mellin formula, use `mellin_theta` on $\mathbb R^m$
with weight $\exp(-\sum_j\tau_j)$, separate the product by Fubini, and
substitute $t=\exp\tau$ in each remaining Mellin integral. The auxiliary
`mconv_neg` is the change of variables $\tau\mapsto-\tau$, giving
$H_{-\varepsilon}=H_\varepsilon$.

## Theta integral of a convolution

Let $(X,\mu)$ be a measurable space with an s-finite measure,
$F:X\to\mathbb C$ a.e. strongly measurable, and $\delta_i:X\to(0,\infty)$
measurable, with

\[
 \int_X |F(x)|\bigl(\textstyle\prod_i\delta_i(x)\bigr)^M\,d\mu(x)<\infty
\]

in the sense of `Integrable` for a real $M$. For $a>0$ and
$\varepsilon\ne0$, set $b_0=a\exp(-\varepsilon\sum_j\tau_j)$ and
$b_j=\exp(\varepsilon\tau_j)$ ($j\ge1$), so $\prod_i b_i=a$. The second
part of the statement (`theta_mconv`) is

\[
 \int_X F(x) H_\varepsilon\bigl(a\textstyle\prod_i\delta_i(x)\bigr)\,d\mu(x)
 = \int_{\mathbb R^m}\int_X F(x)\prod_i h_i(b_i\delta_i(x))\,d\mu(x)\,d\tau .
\]

At fixed $x$, translate the log coordinates by
$(\log\delta_j(x)/\varepsilon)_{j=1}^m$. The translated convolution
integrand uses the scale $a\prod_i\delta_i(x)$ in the distinguished factor,
and the other factors absorb the translation. Translation invariance
identifies the two fibers, also for the integral of the absolute value.
The bound above and the assumed product-weight integrability give
integrability on $X\times\mathbb R^m$, so Bochner Fubini applies. The
opposite parametrization ($\varepsilon=-1$ instead of $1$) is useful
when all scales are inverted.

## Source and scope

Hervé Jacquet, *Archimedean Rankin–Selberg integrals* (2009),
`jacquet-2009-archimedean-rankin-selberg`, p. 28, §4.4, proof of
Proposition 4.3. That proof convolves two pairs and rewrites the integral
against the convolution as an integral of independently scaled pair tests.
Here those convolution and Fubini steps are derived for a nonempty finite
list in real log coordinates, without invoking a functional equation and
with an explicit integrability hypothesis. The statement does not claim
that arbitrary Mellin pairs are sums of convolutions, or assert the
continuation conclusion of Jacquet's proposition.
