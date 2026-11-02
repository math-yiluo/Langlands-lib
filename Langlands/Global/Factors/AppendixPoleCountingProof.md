# Finite shifted-factor pole counting

This module proves
`Langlands.Global.PoleComparison.AppendixPoleCountingStatement`
with `appendixPoleCounting`. Its three components are
`symmetricBlockShift`, `appendixExtremePole`, and `appendixBlockRigidity`.
The target and its imports are unchanged.

The final theorem is universally quantified as
`appendixPoleCounting (I : Type u) [Fintype I] [Nonempty I] :
AppendixPoleCountingStatement I`, for an arbitrary universe `u`.
The shift theorem requires only the explicitly supplied attained maximum;
the extreme-pole theorem also uses finiteness; the rigidity theorem uses
nonemptiness to choose a maximum.

The proof uses the attained maximum of half the segment length plus its
real exponent. The partner symmetry makes the maximum nonnegative. The
open exponent interval bounds every pair-factor shift below by minus one,
and the two height bounds bound it above by twice the maximum. A maximal
block paired with its partner attains the upper bound at the index zero.

The analytic argument uses the actual finite product in the statement.
Translation preserves the order of each base function, and the order of
the product is the sum of these orders. The real meromorphy and nonpositive
orders supplied for the base factors rule out cancellation of the
strictly negative partner order at the extremal point. More precisely,
each finite sum of nonpositive orders is at most the selected summand.
Applying this observation at the three product levels preserves the
negative order of the maximal block's partner factor at index zero.
Orders take values in `WithTop ℤ`; the nonpositive-order premise excludes
infinite order, while the separate meromorphy premise excludes reliance
on the order assigned to a nonmeromorphic function.

At minus twice the maximum height, every reflected shifted argument is
strictly positive. The positive-real base-factor hypotheses and analytic
affine composition therefore make the reflected finite product a
holomorphic unit. The product of this unit and the epsilon unit has order
zero. Multiplying by the inverse denominator gives the negative of the
denominator's order. This is strictly positive, so the gamma function has
a zero as a meromorphic germ.
Here the reflected expression is exactly `blockLFactor length exponent
base (1 - z)`, and gamma is exactly epsilon times that expression divided
by `blockLFactor length exponent base z`.

Finiteness and nonemptiness provide an attained maximum for the rigidity
component. The assumed restriction on real gamma zeros forces minus
twice this maximum to equal zero. The heights of each block and its
partner are then nonpositive. Their sum is the natural length parameter,
so that length vanishes, and the opposite exponents both vanish as well.

The source is Henniart, *Une preuve simple des conjectures de Langlands
pour GL(n) sur un corps p-adique* (2000), Appendix A.1–A.3, printed
pp.453–454, registered as `henniart-2000-simple-proof`. The finite
pair-factor shifts and partner symmetry come from that passage. The
implemented proof uses the lower bound minus one for all shifts to
exclude reflected numerator cancellation, rather than the printed
most-positive-pole assertion.
The original PDF pages 15–16 have SHA-256
`be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
The maximum-height bounds and the explicit analytic noncancellation
argument are derived content, not separately stated results of the paper.

Worker 64 authored the starting Lean proof and its explanation in H1
shared draft revision 5. Worker 359 retained that proof, checked it against
the published target and original source passage, and expanded this
explanation.

This is a conditional analytic consequence for the actual finite product
defined in the statement. It assumes the base-factor meromorphy and
nonpositive real orders, positive-real holomorphic nonvanishing, matched
partner poles, epsilon units, and the real gamma-zero restriction.
Representation classification, actual pair-factor formulas, factor and
measure existence, and the arithmetic gamma comparison remain application
inputs. The parent program retains the global functional-equation and
boundary-nonvanishing obligations; no local or global correspondence is
proved by this module.
