# Order-linear formal comparisons across principal covers

`BasicAtlas.OrderAction.Comparison E E'` records an actual formal
isomorphism commuting with the whole order after refining two formal
atlases to a common principal cover. It constructs a D-linear equivalence
of their complete compatible-family modules and natural isomorphisms on
coefficient algebras and on Nilp.

## Provenance and scope

This is derived coordinate infrastructure for Drinfeld's convention of
formal groups glued over localizations: Drinfeld, *Coverings of p-adic
symmetric regions* (1976), printed p.109, paragraph immediately before
section 2 (PDF page 3). The registered source is
`drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
That paragraph supplies the gluing convention; this module's constructions
are internal consequences of the existing formal-map and refinement APIs.

O and R are arbitrary commutative rings with `Algebra O R`. D is a ring
with `Algebra O D` and need not be commutative. The two finite coordinate
types lie in `Type` and can differ. Covers can be infinite: their principal
generators span the unit ideal. Coefficient tests lie in R's universe v,
and complete-family modules lie in v+1. Actual chart laws, order actions
and common-refinement formal isomorphisms are supplied.

This unit constructs no comparison without those formal data and asserts
no characterization of all natural point-functor isomorphisms. It contains
no quotient of presentations, height descent, framing, moduli object or
representability result.

## Actual formal comparison data

`Comparison` contains a `CoverRefinement` of each original atlas, equality
of the finer covers, and an `OrderAction.Iso` between the restricted order
actions. That isomorphism consists of two actual formal atlas maps,
commutation equations for every d in D, and both formal inverse equations.
An equivalence of point sets is not part of the input.

`toBasicComparison` retains exactly those refinements and underlying formal
maps, forgetting only order commutation. Its inverse equations are the
underlying equalities obtained from the order-linear equations.
`ofCommon` uses the existing product-generator principal cover and its
two genuine containment refinements. Its remaining input is the actual
order-linear formal isomorphism on that cover.

## Realization on complete compatible families

`onPoints A` restricts an E-family along the left refinement, evaluates
the formal isomorphism, and applies the inverse right refinement
equivalence. This last inverse uses actual coefficient gluing from
`AtlasRefinementPoints`. All three maps are D-linear equivalences.
`onPoints_toBasicComparison` identifies the underlying function with the
existing O-linear comparison. `onPoints_restrict` characterizes the
constructed map after restriction to the right refinement: it is evaluation
of the formal forward map on the restricted left family. Both formulas
hold for every complete compatible family.

`pointFunctorIso` composes the corresponding natural isomorphisms in that
order. `pointFunctorIso_hom_app` identifies its forward component with
`onPoints`; `onPoints_natural` applies its naturality equation to an
individual family. `nilpPointFunctorIso` restricts the same isomorphism
along `Nilp.forget R π`, so its tests are actual R-algebras in which the
image of π is nilpotent.
