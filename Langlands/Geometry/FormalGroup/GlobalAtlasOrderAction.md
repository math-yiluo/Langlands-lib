# Global order actions and their formal coordinate atlases

This derived unit restricts an actual global formal order action to every
principal-open cover and proves that its singleton atlas has the original
order-module point functor.

## Provenance and scope

Drinfeld, *Coverings of p-adic symmetric regions* (1976), printed p.109
(PDF page 3), first permits formal groups glued over localizations in the
paragraph before section 2, then defines formal O_D-modules in section 2 A.
The registered source is
`drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
The present constructions are internal consequences of `OrderAction`,
`AtlasOrderAction` and `GlobalAtlas`; they are not separately numbered
theorems of the source.

O and R are commutative rings, R is an O-algebra, D is a possibly
noncommutative O-algebra, and the coordinate type is fixed and finite in
`Type`. The coefficient tests have R's universe v. Original point modules
lie in v, and atlas compatible families lie in v+1. Restriction works for
any supplied principal-open cover; the global point comparison concerns
the singleton cover at 1. No division-order specialization, special tangent
condition, height, refinement invariance, formal-scheme comparison, moduli
construction or representability is asserted.

## The original order-module point functor

`ModuleLaw.OrderAction.AlgebraPoint E A` is the module of nilpotent tuples
for E after extending coefficients from R to A. Its D-action is evaluation
of the actual extended formal endomorphisms.
`algebraMapPoints` uses the original coefficient map on tuples and proves
D-linearity by coefficient naturality of each actual global endomorphism.
`algebraPointFunctor` packages these maps into the functor to D-modules;
identity and composition follow from the existing coefficient-map laws.
`nilpAlgebraPointFunctor` restricts this functor to R-algebras in which the
image of a supplied element pi is nilpotent.

## Restricting the global action

`BasicAtlas.globalOrderChart_coordinates` proves that extending a global
order endomorphism first to R[1/a] and then to a test A gives the original
endomorphism's series extended directly to A. Coefficient composition and
the localization coefficient triangle give the equality.

`globalOrderChartIso` upgrades the existing actual formal chart comparison
to an order-linear formal isomorphism. In both directions the coordinate
map is the identity. Its two order-commutation equations reduce to the
preceding coefficient formula; its inverse equations are those of the
original chart comparison.

`ofGlobalCoverOrderAction E s hs` supplies the restricted action on every
chart of `ofGlobalCover`. The formal transition commutation is proved:
the transitions have identity coordinates and both chart actions have the
same directly extended series. `ofGlobalOrderAction` specializes this
construction to the singleton cover.

## The order-linear singleton comparison

`globalOrderPointEquiv` composes the order-linear atlas chart equivalence
with evaluation of `globalOrderChartIso`. It is a D-linear equivalence
from the singleton atlas's compatible families to E's original algebra
points. `globalOrderPointEquiv_apply` proves that it evaluates the family
at the identity test in the distinguished chart, since the final formal
map has identity coordinates. `globalOrderPointEquiv_eq` identifies its
underlying function with the existing O-linear singleton comparison.

`globalOrderPointEquiv_natural` follows from the original coefficient
naturality equation, since both functions and coefficient maps have the
same underlying tuple formulas. `globalOrderPointFunctorIso` packages
these equivalences as a natural isomorphism of D-module functors after
`ModuleCat.uliftFunctor`. The component is the constructed equivalence
followed by `ULift.moduleEquiv.symm`; naturality is the preceding equation
under `ULift.up`. `globalOrderNilpPointFunctorIso` restricts the same
natural isomorphism along the forgetful functor from Nilp.
