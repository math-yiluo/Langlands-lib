# Classes of special formal division-order atlases

`SpecialAtlas.IsoClass` is the quotient of actual special formal
division-order atlases by existence of an actual formal order-linear
isomorphism after principal refinement. Actual special refinement
preserves the class. Every class has a chosen actual special
representative, with its constructed point functors.

## Source and scope

This is derived presentation infrastructure for Drinfeld, *Coverings of
p-adic symmetric regions* (1976), printed p.109 (PDF page 3). The paragraph
immediately before section 2 permits formal groups glued over
localizations. Section 2 A defines special formal division-order modules
using dimension d and distinct geometric tangent characters, then uses
isomorphism classes in its functor. The registered source is
`drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
The comparison quotient and choices here are internal constructions,
rather than a theorem separately stated in that passage.

The parameters are a nonarchimedean local field K, a finite-dimensional
central division K-algebra D, a supplied K-embedding iota of a field L
into D, and a commutative O_K-algebra R. Write d for
`CentralSimple.reducedDegree K D`. Each `SpecialAtlas` has coordinates
`Fin d`, a principal cover whose generators span the unit ideal, an
actual action of `IntegerRing K D`, its unramified full-degree subfield
certificate, and its geometric tangent-character certificates. Covers
may be infinite. Coefficient tests lie in R's universe v and family
modules in v+1; geometric character tests use `max u v`, as in
`SpecialAtlas`.

These are classes of the supplied atlas presentations. This unit proves
neither existence of an unramified subfield nor specialization to
invariant 1/d, and makes no classification claim for arbitrary formal
schemes. No height, framing, varying-base moduli functor or
representability is asserted.

## Actual comparison and refinement

`toOrderPresentation` retains the actual atlas, dimension d and full
division-order action. `Comparison X Y` is exactly
`BasicAtlas.OrderAction.Comparison X.order Y.order`: two actual
refinements to equal finer generator sets, and actual inverse formal
maps commuting with every division-order element on those refinements.
It is not a point-set equivalence supplied as substitute data.

`Equivalent` records nonemptiness of that comparison type. The existing
actual reflexive, reversed and composed comparisons prove the setoid
laws, giving `comparisonSetoid` and `IsoClass`. `classOf_eq_iff` is the
quotient equality criterion, and `classOf_eq_of_comparison` applies it to
a specified actual formal witness.
`equivalent_toOrderPresentation` keeps precisely that witness, allowing
`IsoClass.forgetSpecial` to descend the underlying order-linear class.

`comparisonOfRefinement X q` uses the actual generic
`Comparison.ofRefinement X.order q`, whose formal maps compare direct
with successive restriction. `comparisonOfRefinement_onPoints`
identifies its map on every complete compatible family with the
constructed `refinementPointEquiv`, including its coefficient-gluing
inverse. Applying the quotient criterion gives `classOf_refine`.

## Chosen special representatives

`IsoClass.representative` uses `Quotient.out` within the type of actual
special atlases, retaining the representative's own special
certificates. `classOf_representative` identifies its class.
`pointFunctor` evaluates its actual compatible-family division-order
module functor. `nilpPointFunctor` restricts that same functor to
coefficient algebras where the specified element of R is nilpotent.

`comparisonToRepresentative` chooses an actual refined formal
comparison using the quotient equality criterion. Its constructed
natural isomorphisms are `pointFunctorIsoToRepresentative` and
`nilpPointFunctorIsoToRepresentative`. `comparisonOfClassEq` similarly
chooses an actual formal comparison from class equality.

The representative functors and comparison maps depend on these
explicit classical choices. Different actual formal comparison
witnesses can induce different automorphisms; class equality alone
specifies no canonical point map.
