# Equivalence operations on order-linear formal comparisons

`OrderAction.Comparison.refl`, `symm` and `trans` construct actual
order-linear formal comparisons after refinement. `refine` and `join`
give the intermediate operations. Their evaluated maps obey identity,
inverse, refinement invariance and composition laws on all complete
compatible families.

## Provenance and scope

This is derived infrastructure for the localization-gluing convention in
Drinfeld, *Coverings of p-adic symmetric regions* (1976), printed p.109,
paragraph immediately before section 2 (PDF page 3). The registered source
is `drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
The comparison operations and proofs are internal constructions; the
paragraph is not cited as a separate transitivity theorem.

O and R are arbitrary commutative rings with `Algebra O R`. D is an
O-algebra ring, possibly noncommutative. Coordinates are finite types in
`Type`; they can differ between atlases. Principal covers may be infinite.
Coefficient tests lie in R's universe v and full-family modules in v+1.
The input order actions and formal comparison witnesses are actual data.
No arbitrary equivalence of point sets replaces the formal maps.

## Construction of the actual formal operations

`refl E` uses the reflexive cover refinement on both sides and the
identity formal isomorphism of its restricted order action. `symm`
exchanges the refinements and reverses the two formal maps.

`refine f q` composes both original refinements with the further
refinement q, retargeted to f's right atlas. Its coordinate isomorphism
first compares direct with successive left order restriction, applies the
actual restricted order-linear formal isomorphism, and reverses the
direct-to-successive right comparison. `orderCompIso` and `Iso.restrict`
provide formal order commutation and both inverse equations for these
steps.

`join f g h` applies when the two middle refinements have equal finer
covers. Between f's and g's coordinate maps it inserts the actual
`orderSourceIso` for the two selected original middle charts. Thus even
different source-chart choices are handled by the original
order-compatible formal transition.

`trans f g` refines both witnesses to the product of their left finer
covers, using `commonLeft` and `commonRight`, and then applies `join`.
The product generators span the unit ideal and have the required actual
containment witnesses by the existing common-cover construction.

## Realization and implemented proofs

The five `toBasicComparison_*` equations identify these constructions
with the underlying O-linear formal operations of
`AtlasComparisonEquivalence`. They are definitional equalities of
comparison data, including their actual forward and inverse formal maps.
Forgetting order commutation does not change those maps.

The evaluated identity, inverse, refinement-invariance, join and
transitivity formulas then reuse the underlying full-family formulas.
The actual family functions agree definitionally; their D-linear
structures were constructed in `AtlasOrderComparison`.
`onPoints_symm` is also a definitional equality of D-linear
equivalences. In particular,
`(f.trans g).onPoints A x = g.onPoints A (f.onPoints A x)` for every
complete compatible family x.

Every constructed comparison inherits the coefficient-algebra and Nilp
natural isomorphisms from `AtlasOrderComparison`. These operations
establish existence of the comparisons needed for an equivalence relation.
This unit constructs no quotient, proves no equality of arbitrary
comparison witnesses, and makes no height, framing or representability
claim.
