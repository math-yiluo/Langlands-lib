# Classes of order-linear formal atlas presentations

`OrderAtlasPresentation` bundles an actual finite-dimensional formal
atlas and its full order action. Its `IsoClass` is the quotient by
existence of an actual order-linear formal comparison after principal
refinement. Class equality is exactly existence of such a comparison.
Actual refinements preserve the class.

## Provenance and scope

This is derived presentation infrastructure for Drinfeld's convention of
formal groups glued over localizations: Drinfeld, *Coverings of p-adic
symmetric regions* (1976), printed p.109, paragraph immediately before
section 2 (PDF page 3). The registered source is
`drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
The quotient and representative constructions are internal derived
content, not a separately attributed theorem of that paragraph.

O and R are arbitrary commutative rings with `Algebra O R`; D is an
O-algebra ring and can be noncommutative. Each presentation specifies a
natural-number dimension and coordinates `Fin dimension`. Principal
covers can be infinite and their generators span the unit ideal.
Coefficient tests lie in R's universe v and family modules in v+1.

The quotient concerns these actual finite-coordinate atlas
presentations. It makes no assertion that every formal group has a
presentation of this form, or that every natural point-functor
isomorphism is induced by the formal comparison relation.

## The relation and its quotient

The bundle extends `AtlasPresentation` and adds its actual chart order
action and transition-commutation equations. `Equivalent X Y` means
`Nonempty (OrderAction.Comparison X.order Y.order)`. The actual formal
`refl`, `symm` and `trans` constructions establish the three relation laws;
they define `comparisonSetoid` and hence `IsoClass`.

`classOf` is the quotient map. `classOf_eq_iff` is the quotient equality
criterion. `classOf_eq_of_comparison` applies it to a supplied actual
formal witness. `equivalent_forgetOrder` retains the same underlying
formal maps, and `IsoClass.forgetOrder` descends the underlying
`AtlasPresentation` to its O-linear class.

## Actual refinement invariance

`OrderAction.Comparison.ofRefinement E q` is an actual comparison with
`q.orderAction E`. Let r be the reflexive refinement of q's atlas. The
comparison uses the composed left refinement `q.comp r`, the right
refinement r, and `q.orderCompIso E r`. Thus it supplies formal maps and
their inverse and full-order commutation equations.
`onPoints_ofRefinement` applies the right refinement equivalence's
injectivity and the direct-to-successive restriction formula to identify
this comparison's full-family map with `q.orderPointEquiv E A`.

`refine X q` keeps X's dimension and uses q's actual atlas and restricted
order action. `classOf_refine` identifies its class with X's using the
constructed formal comparison.

## Chosen representatives and functors

`IsoClass.representative` chooses an actual presentation by `Quotient.out`.
`classOf_representative` identifies its class. The class's `pointFunctor`
and `nilpPointFunctor` evaluate that chosen representative's actual
D-module family functors.

`comparisonToRepresentative` chooses an actual formal comparison from the
quotient equality criterion. Its realized algebra and Nilp natural
isomorphisms are `pointFunctorIsoToRepresentative` and
`nilpPointFunctorIsoToRepresentative`. `comparisonOfClassEq` similarly
chooses an actual formal comparison from a supplied equality of classes.

These functors and comparisons depend on the stated choices. Distinct
formal comparison witnesses can induce different automorphisms; no
canonical point map follows from mere class equality. This unit makes no
height, special-tangent, framing, moduli or representability claim.
