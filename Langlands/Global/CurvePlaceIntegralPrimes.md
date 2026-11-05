# Integral-closure primes and all actual upper curve places

This construction identifies the primes of the actual integral closure of a
lower curve-place valuation ring with **all** actual upper curve places. It
compares their ramification indices and residue degrees and transfers the
fundamental degree identity to that original place index.

## Source and scope

Brian Conrad, *Weil and Grothendieck approaches to adelic points*, December 31,
2011, Example 4.2, printed p.10, uses the completed-tensor product over all upper
places. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The present arithmetic is a derived prerequisite for that comparison; Conrad
does not separately state this prime/place equivalence there.

Let `k`, `K` and `L` be fields in one arbitrary universe, with the three algebra
structures, and let `p : AlgebraicCurve.Place k K`. Write `R` for the original
`p.toValuationSubring` and `S` for `curvePlaceIntegralClosure L p`, the actual
integral closure of `R` in the original upper field `L`. An upper place is an
element of `CurvePlacesAbove k L p`: an original discrete place of `L` whose
valuation subring has comap exactly `R` along the original field embedding.

The inclusion and center constructions need only these fields and algebra
structures. The prime classification, localization and invariant comparisons
use finite `k`, the supplied original `RatFunc k`-algebra presentation of `K`,
`IsScalarTower k (RatFunc k) K`, `FunctionField k K`, and
`FiniteDimensional K L`. The prime-to-place construction, equivalence and final
place-indexed identity also use `IsScalarTower k K L`. No separability of either
extension or original presentation, no selected upper places, no supplied
normalization finiteness and no supplied prime/place equivalence is assumed.

## Original inclusions and centers

All declarations below are in `Langlands.Global.CurvePlaceIntegralPrimes`.
`integralClosure_le` proves that `S` lies inside every original upper valuation
ring. An element integral over `R` is integral over that upper valuation ring,
which is integrally closed in `L`; hence it is an element of that ring.

`integersMap p q` is the resulting `R`-algebra homomorphism. On underlying
elements it is literally the inclusion in `L`. Scoped instances give its
algebra, the two compatible scalar towers, and torsion freeness. The algebra
instance has priority 50 so the canonical algebra on a valuation ring's own
fraction field keeps precedence.

`center p q` is the comap of the original upper maximal ideal along this
inclusion. It is prime and lies over the original lower maximal ideal.
`centerAbove p q` packages that actual ideal in the full `Ideal.primesOver`
subtype. The upper maximal ideal also lies over this center. These are
statements about the original ideals and original maps.

## Classification by all primes

`heightOne p P` regards a prime `P` of `S` over the lower maximal ideal as a
nonzero height-one prime. The finite integral-closure and Dedekind properties
come from `CurvePlaceIntegralClosure`, including the inseparable case.
Nonzeroness follows from exact lying-over of the nonzero lower maximal ideal.

`upperPlace p P` applies the existing `Place.ofHeightOneSpectrum` to that prime.
The constant-field tower supplies its original constants. The generic
`HeightOneSpectrum.valuation_liesOver` formula says that restriction of this
valuation is the lower adic valuation raised to a nonzero ramification
exponent. Taking the condition value at most one therefore proves equality of
the valuation-subring comap with `R`. This constructs an element of the full
original `CurvePlacesAbove` subtype.

`valuationSubringAtCenter p q` identifies the localization valuation subring
at `centerAbove p q` with the original upper valuation subring itself. For a
fraction `a/b` in this localization, `a` belongs to the upper ring and `b` has
unit image because it is outside the center. This proves containment. The
localization has dimension at most one; the original upper valuation ring is
proper, so the valuation-overring equality theorem gives equality.
`localizationAtCenter` transports the actual localization structure along the
resulting explicit algebra equivalence.

`upperPlace_center` then recovers every original upper place. Injectivity uses
the existing injectivity of the original `Place.ofHeightOneSpectrum` map.
`primeEquivUpperPlaces p` is the resulting equivalence from every prime of `S`
over the lower maximal ideal to every original upper place. Its `_apply` law
identifies the forward map literally with `Place.ofHeightOneSpectrum`, its
`_symm_apply` law identifies the inverse with `centerAbove`, and
`centerAbove_upperPlace` records the inverse identity on primes.

## Invariants and the fundamental identity

`localization_ramificationIdx` proves that the ramification index of the upper
maximal ideal over its center in `S` is one. Its ideal is exactly the image of
the center under localization. The Dedekind multiplicity definition gives
index one for this image, and Mathlib's comparison transfers that result to the
localized-length definition of ramification index.

`localization_inertiaDeg` proves that the corresponding residue degree is one.
The canonical residue-field homomorphism is bijective because localization is
surjective on stalks. Its degree is therefore one. No residue-field
cardinality is assumed. `ramificationIdx_center` and `inertiaDeg_center` now
use multiplicativity in the tower `R -> S -> q.toValuationSubring`; localization
supplies the flatness required for the ramification tower formula. Thus both
invariants at the original upper place equal the invariants at its center.

`sum_ramification_inertia` reindexes the existing integral-closure fundamental
identity through `primeEquivUpperPlaces`, using these two invariant
comparisons. The sum runs over every `q : CurvePlacesAbove k L p`, and equals
`Module.finrank K L`. Finiteness of this original place index is proved in
`CurvePlaceCompletedProduct`; no finite subfamily is substituted for it.

## Dependencies and retained obligations

The module reuses the actual integral closure, the original completion
extension's valuation-ring algebra, Mathlib's Dedekind localization and
ramification theory, and the actual curve-place constructors. All ring and
place comparisons are proved on these objects. The route through normalized
charts and finite integral closure retains arbitrary original inseparability.

This unit establishes neither completed-tensor injectivity nor a Weil point
homeomorphism. Combining the fundamental identity with the completed local
lower bound and the simultaneous tensor surjection is the next step. Integral
models and the global adelic comparison remain separate obligations.
