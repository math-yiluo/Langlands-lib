# Entire normalizations from a Mellin pair with a power Gaussian factor

## Statement

`MellinPairPowerNormalizedGrowthStatement` concerns two weighted integrals
\(Z(s)=\int_X F(x)\,\delta(x)^s\,d\mu(x)\) and \(Z^\vee(s)=\int_Y G(y)\,\delta^\vee(y)^s\,d\nu(y)\)
over s-finite measure spaces, with positive measurable weights \(\delta,\delta^\vee\). The
integrals \(\int\|F\|\delta^\sigma\) and \(\int\|G\|(\delta^\vee)^\sigma\) are assumed finite for
every real \(\sigma\ge N_0\). It also takes a measurable, rapidly decreasing pair \(h,k\) on
\((0,\infty)\) that satisfies the theta identity
\(\theta(F,\delta,h)(a)=a\,\theta(G,\delta^\vee,k)(a^{-1})\) for all \(a>0\). Here \(\theta\) is
the Library's `ArchimedeanMellinPair.theta`. The two Mellin transforms of the pair are assumed to
have the form

- \(\mathcal M h(-s)=\varepsilon\,\exp(s^2)^p\,D(s)\),
- \(\mathcal M k(s-1)=\exp(s^2)^p\,D^\vee(1-s)\),

for every \(s\in\mathbb C\). In these formulas \(p\) is a natural number, \(\varepsilon\neq0\) is a
constant, and \(D,D^\vee\) are functions of exponential growth in vertical strips (the Library's
`HasStripExponentialGrowth`).

The conclusion gives two entire functions \(N,N^\vee\), both of exponential growth in vertical
strips, such that

- \(N(s)=D(s)\,Z(s)\) and \(N^\vee(s)=D^\vee(s)\,Z^\vee(s)\) whenever \(\operatorname{Re}s\ge N_0\);
- \(N^\vee(1-s)=\varepsilon\,N(s)\) for every \(s\in\mathbb C\).

The module also proves two public closure properties of `HasStripExponentialGrowth`, in the
namespace `Langlands.LocalFactor.Archimedean`:

- `HasStripExponentialGrowth.comp_one_sub`: the property is preserved by \(s\mapsto 1-s\).
- `HasStripExponentialGrowth.finset_prod`: the property holds for a finite product of functions
  that each have it.

The main proof uses `comp_one_sub`. `finset_prod` is a general closure property and is not used
in this module.

## Proof

Set \(R(s)=\varepsilon^{-1}\exp(-s^2)^p\,\mathcal M\theta(-s)\), where \(\theta\) is the theta
function of the pair. The Library theorem `mellin_theta_entire` shows that \(\mathcal M\theta(-s)\)
is entire. It also gives two half-plane formulas: \(\mathcal M\theta(-s)\) equals
\(\mathcal Mh(-s)Z(s)\) for \(\operatorname{Re}s\ge N_0\), and
\(\mathcal Mk(s-1)Z^\vee(1-s)\) for \(\operatorname{Re}s\le 1-N_0\). By the transform
hypotheses and \(\exp(-s^2)^p\exp(s^2)^p=1\), \(R\) is entire, with

- \(R(s)=D(s)Z(s)\) for \(\operatorname{Re}s\ge N_0\);
- \(R(s)=\varepsilon^{-1}D^\vee(1-s)Z^\vee(1-s)\) for \(\operatorname{Re}s\le 1-N_0\).

The proof then shows that \(R\) has exponential growth in vertical strips. It uses three bounds.

1. **Gaussian bound on any strip.** By `theta_rapidDecay`, the theta function decays rapidly, so
   its Mellin transform at \(-s\) is bounded on every vertical strip. The bound comes from
   dominating the integrand by a fixed integrable function on \((0,1]\) and on \((1,\infty)\).
   Since \(\|\exp(-s^2)^p\|=\exp(p((\operatorname{Im}s)^2-(\operatorname{Re}s)^2))\le
   \exp(p(\operatorname{Im}s)^2)\), \(R\) is at most a constant times
   \(\exp(p(\operatorname{Im}s)^2)\) on each strip.
2. **Right vertical lines.** On a line \(\operatorname{Re}s=b\) with \(b\ge N_0\), the integral
   \(Z(s)\) is bounded in norm by \(\int\|F\|\delta^b\). Together with the growth of \(D\), this
   bounds \(R\) by \(C\exp(K|\operatorname{Im}s|)\) for \(|\operatorname{Im}s|\ge T\). Since \(R\)
   is continuous, it is bounded on the compact segment \(|\operatorname{Im}s|\le T\), and the
   exponential bound extends to the whole line.
3. **Left vertical lines.** The same argument works on a line \(\operatorname{Re}s=a\) with
   \(a\le1-N_0\). It uses the left formula, the growth of \(D^\vee\) on the reflected line, and the
   bound \(\int\|G\|(\delta^\vee)^{1-a}\).

Fix a strip \(a\le\operatorname{Re}s\le b\). Choose a left line \(l<\min(a,1-N_0)\) and a right
line \(r>\max(a,b,N_0)\). On the strip between them, \(R\) is entire, has exponential bounds on
both edge lines, and has a Gaussian bound inside. The Library's Phragmén–Lindelöf lemma
`norm_le_exp_of_gaussian_on_strip` then gives an exponential bound for
\(|\operatorname{Im}s|\ge1\), which proves `HasStripExponentialGrowth R`.

Finally, the proof takes \(N=R\) and \(N^\vee(t)=\varepsilon R(1-t)\). Then \(N^\vee\) is entire,
and it has strip growth by `comp_one_sub` and multiplication by a constant. The reflection
\(N^\vee(1-s)=\varepsilon R(s)=\varepsilon N(s)\) holds by definition. For
\(\operatorname{Re}t\ge N_0\), the left formula at \(1-t\) gives
\(N^\vee(t)=\varepsilon\cdot\varepsilon^{-1}D^\vee(t)Z^\vee(t)=D^\vee(t)Z^\vee(t)\).

## Provenance

This generalizes the Library theorem `mellinPairNormalizedStripGrowth`
(`ArchimedeanMellinPairStripGrowth`) in two ways.

- **Power of the Gaussian.** The Gaussian factor \(\exp(s^2)\) becomes a power \(\exp(s^2)^p\).
  This is Jacquet's quadratic exponential \(e^{P(s)}\) with \(P(s)=ps^2\).
- **General denominators.** The reciprocal \(L\)-denominators and the signed epsilon factor
  become arbitrary functions \(D,D^\vee\) of exponential strip growth and a nonzero constant
  \(\varepsilon\).

A power of the Gaussian appears when a pair is built by convolving several rank-one pairs, each
of whose Mellin transforms carries one factor \(\exp(s^2)\).

The analytic argument follows Jacquet, *Archimedean Rankin–Selberg integrals* (2009), §4.2 and
Proposition 4.1 (author version pp. 22–25). There, a theta identity for a Mellin pair gives
continuation, and Phragmén–Lindelöf is applied in vertical strips. As in the Library's
`mellinPairNormalizedStripGrowth`, the Lean proof applies Phragmén–Lindelöf directly to the
normalized function \(R\). It uses the assumed strip growth of \(D\) and \(D^\vee\) on the edge
lines, not Jacquet's Stirling ratio bound. The theta identity and the shape of the pair's Mellin
transforms are hypotheses of the statement.
