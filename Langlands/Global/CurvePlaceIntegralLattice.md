# The actual integral lattice in all upper completions

This module characterizes the original integral closure by integrality at every
actual upper curve place, then identifies its closure in the product of the
actual upper completions. The resulting lattice is exactly the full product
of the original completed integer rings.

## Source and hypotheses

Brian Conrad, *Weil and Grothendieck approaches to adelic points*, December 31,
2011, Example 4.2, printed p.10, uses integral models to pass from local Weil
comparisons to the adelic statement. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The present lattice description is a derived arithmetic prerequisite for that
integral comparison; it is not attributed as a separately stated theorem of
Conrad.

The fields `k`, `K` and `L` lie in one arbitrary universe. For the integral
criterion and closure identity, the hypotheses are finite `k`, their three
algebra structures, `FiniteDimensional K L`, `IsScalarTower k K L`, an original
`Algebra (RatFunc k) K` presentation, `IsScalarTower k (RatFunc k) K`, and
`FunctionField k K`. Fix any original `p : AlgebraicCurve.Place k K`. Let
`R = p.toValuationSubring` and `S = curvePlaceIntegralClosure L p`. Neither
extension nor the rational-function presentation is assumed separable. The
index is the full `CurvePlacesAbove k L p` subtype, not a chosen finite family.

## Actual integral membership

In `Langlands.Global.CurvePlaceIntegralLattice`, `integral_mem_iff p x` says
that `x` is an element of the actual `S` if and only if it belongs to the
original valuation subring of every original upper place.

The forward implication uses the proved inclusion of `S` in every upper
valuation ring. For the reverse implication, take any nonzero height-one
prime of the actual Dedekind domain `S`. Its ideal is maximal. Integrality of
`S/R` makes its contraction maximal in the local ring `R`, hence equal to the
original lower maximal ideal. The original prime-to-place construction
therefore supplies an upper place. The hypothesis puts `x` in the localization
valuation subring at this prime. A Dedekind domain is the intersection of these
localizations inside its original fraction field `L`; this is Mathlib's
`HeightOneSpectrum.iInf_localization_eq_bot`. Thus `x` lies in the image of
`S` in `L`, giving its original integral-closure membership.

## Closure of the original embedding

`integralEmbedding p` sends an actual `a : S` to
`fun q => algebraMap L (curvePlaceCompletion q.1) (a : L)`.
It is a ring homomorphism on the original elements. The `_apply` law is
literal. This map and its law require only the field and algebra structures;
no finiteness or global-function-field premise is used in their definitions.

`productIntegers_isOpen` proves that the full product of completed integer
rings is open in the product of completed fields. Here only
`FiniteDimensional K L` is needed in addition to the field/algebra structures:
the existing construction has already proved finiteness of the whole
upper-place index. Each completed integer ring is open for its original
valuation topology.

`productIntegers_subset_closure` uses the existing weak-approximation density
of the diagonal original `L` in the product of all upper completions. The
intersection of a dense range with an open set is dense in that open set.
For this open integer lattice, every original diagonal element in the
intersection is integral at all upper places, hence belongs to `S` by the
proved criterion. This gives approximation by actual integral-closure
elements throughout the lattice.

`closure_integralEmbedding` proves equality of the closure of the original
`S` image with the full product integer lattice. The preceding approximation
gives one containment. The other follows because each original `S` element
maps to integers in every completion, and the product integer lattice is
closed. No independent choice of approximate integers or unproved integral
weak-approximation principle is supplied.

## Reuse and retained obligations

The module reuses the actual finite integral closure, the proved original
prime/upper-place map, Mathlib's localization intersection theorem, original
field weak approximation, and the original/completed integrality comparison.
It does not yet assert an integral tensor isomorphism, integral Weil point
homeomorphism or adelic comparison. The lattice closure is intended as the
density input for the integral tensor comparison; its closed-image and
injectivity arguments remain separate obligations.
