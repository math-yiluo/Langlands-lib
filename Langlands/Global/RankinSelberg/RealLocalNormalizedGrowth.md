# Entire normalized pairs for the real rank induction

This module introduces the real counterpart of the complex induction currency
`ComplexJacquet.HasComplexPairNormalizedGrowth` from `ComplexLocalNormalizedGrowth`. It is the
form in which the real unequal-rank induction carries its local functional equations.

## The definition

`RealJacquet.HasRealPairNormalizedGrowth ds es dds ees b c hc sign I Id` says the following.
Here `ds`, `es` (primal) and `dds`, `ees` (dual) are real block lists, `b` is a real unit,
`c` is a positive real scale, `sign` is a complex number, and `I`, `Id` are complex functions.
There exist two functions `N` and `Nd` with these properties:

- `N` and `Nd` are entire (complex differentiable everywhere);
- both have `HasStripExponentialGrowth`: on every closed vertical strip and away from a bounded
  range of imaginary parts, they are bounded by `C * exp (K * |Im s|)`;
- on some right half-plane `σ < Re s`, `N s` is the reciprocal real pair `L`-factor
  `(realPairLFactor ds es).denominator s` times `I s`, and `Nd s` is
  `(realPairLFactor dds ees).denominator s` times `Id s`;
- for every complex `s`, `Nd (1 - s) = sign * realPairEpsilon ds es b c hc s * N s`.

So `N` and `Nd` are the integrals divided by their `L`-factors, continued to entire functions,
and they satisfy the functional equation everywhere with no remaining Gamma factors.

## Provenance

This is an internal induction predicate. It is a real port of the Library's complex predicate
`HasComplexPairNormalizedGrowth`, which the complex unequal-rank induction (`ComplexUnequalGrowthInduction`) uses. The
mathematical model is the normalized form of Jacquet, *Archimedean Rankin–Selberg integrals*
(2009), Theorem 2.1 (ii)–(iii). There each integral is a holomorphic multiple of
`L(s, σ_u ⊗ σ'_{u'})` and satisfies the functional equation with the factor
`γ = ε · L(1 - s, dual) / L(s)`. Dividing by the `L`-factors turns that equation into the
everywhere identity above. The growth condition is weaker than Jacquet's boundedness in
vertical strips: the predicate asks only for exponential growth in `|Im s|`. This is the
property the Mellin-convolution and theta arguments of the complex induction need and keep.
The predicate does not claim that the given integrals have any such normalization; it is only
a hypothesis or conclusion of later theorems.

## Closure lemmas

- `congr`: the predicate depends only on the values of `I` and `Id` on a right half-plane. The
  same `N`, `Nd` work with the half-plane `max σ τ`.
- `zero`: the pair `(0, 0)` has the zero normalization.
- `add`: adding normalizations gives a normalization of the sum, on the larger of the two
  half-planes. The functional equation is linear.
- `const_mul`: multiplying `I`, `Id`, `N` and `Nd` by one complex constant `z` keeps every
  property.
- `sum`: finite sums over a `Finset`, by induction from `zero`, `add` and `congr`.

## From normalized pairs to continuation packages

`continuationPackage` derives the Library's `RealJacquet.ContinuationPackage`. Its continuation
factors are the reciprocals of the two reciprocal `L`-factors, its epsilon is
`realPairEpsilon ds es b c hc` and its sign is `sign`. The continuations are `N / den` and
`Nd / den_d`. They are meromorphic on all of `ℂ` because each is an entire function times the
inverse of an entire function. Both denominators are nonzero on a right half-plane
(`ArchimedeanRealPairFactor.realLFactor_ne_zero`). On the intersection of that half-plane with
the agreement half-plane, each continuation equals the original integral. The multiplied-out
equation `den(s)⁻¹ * Md(1-s) = sign * ε(s) * den_d(1-s)⁻¹ * M(s)` holds at every point, not
only codiscretely. Substituting the normalized equation for `Nd (1 - s)` makes both sides equal
as a commutative ring identity in which the inverses are treated as atoms, so `ring` closes it
with no nonvanishing hypothesis.

`unequalContinuation` and `equalContinuation` specialize this. When the integrals are the exact
`realUnequalIntegral`/`realUnequalDualIntegral` (or `realEqualIntegral`/`realEqualDualIntegral`)
and the scale is `sqrt ‖a‖`, the resulting package is literally `UnequalContinuation` (or
`EqualContinuation`). These are the conclusion shapes of the target statement
`RealLocalUniformUnequalContinuationStatement` and of its equal-rank companion.

## The converse bridge

`normalizedEquation_of_continuationPackage` starts with a continuation package for these
factors and two entire functions `N`, `Nd`. These agree with `den * I` and `den_d * Id` on a
right half-plane. It concludes that the normalized equation holds at every point. The proof:

1. A private lemma `eq_codiscrete_of_halfPlane` shows the following. Two functions meromorphic
   on `ℂ` that agree on a right half-plane agree on the codiscrete filter. Their difference has
   meromorphic order `⊤` at a point of the half-plane, and so at every point, because `ℂ` is
   preconnected.
2. This gives `N = den * M` and `Nd = den_d * Md` codiscretely, where `M`, `Md` are the
   package's continuations.
3. The two denominators are nonzero codiscretely
   (`ReciprocalEntire.denominator_eventually_ne_zero`). The reflection `s ↦ 1 - s` preserves
   codiscrete statements (`CuspidalPairPartialGammaGlobal.eventually_codiscrete_one_sub`).
   Combining these with the package's codiscrete equation and cancelling `den(s)` gives
   `Nd (1 - s) = sign * ε(s) * N s` codiscretely.
4. Both sides are continuous: `Nd`, `N` are entire, and the epsilon factor is differentiable by
   `differentiable_realEpsilon`. Every punctured neighbourhood filter lies below the codiscrete
   filter, so uniqueness of limits gives the equation at every point.

`hasRealPairNormalizedGrowth_of_continuationPackage` adds the strip-growth hypotheses on `N` and
`Nd` and packages the result as `HasRealPairNormalizedGrowth`. Inductive steps can therefore
use a smaller-rank continuation package together with growth bounds proved separately.
