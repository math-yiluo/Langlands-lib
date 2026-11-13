# Atlases induced by globally coordinated formal modules

This derived construction restricts a global formal O-module law to every
principal-open cover and constructs its actual formal transition isomorphisms.
For the singleton cover at 1 it proves a natural equivalence with the original
nilpotent-point functor, including the universe lift required by atlas families.

## Provenance and boundaries

Drinfeld, *Coverings of p-adic symmetric regions* (1976), printed p.109
(PDF page 3), paragraph immediately before section 2, permits formal groups
glued from formal groups over base localizations. The registered source is
`drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
This unit is a derived example and comparison for `BasicAtlas`, using the
localization universal property and coefficient coherence. It does not claim
to formalize a separate numbered theorem of the source.

Here O and R are commutative rings with an O-algebra structure on R, σ is a
fixed finite coordinate type, and all test R-algebras lie in R's universe v.
The construction of an atlas works for any supplied principal-open cover,
expressed as `Ideal.span s = top`. The point equivalence and natural isomorphism
below concern the singleton cover at 1. This unit does not prove an equivalence
for arbitrary covers, atlas refinement invariance, a comparison with formal
schemes or Cartier modules, order-action descent, moduli or representability.
No representing or universal object is supplied as input.

## Restricting the global law

`globalCoefficient_comp` proves that the composite R → R[1/a] → A recovers the
original structural coefficient map whenever a is a unit in A. It proves this
by evaluating at every element of R and applying the localization-lift formula.

`globalChartIso M a A ha` compares the law obtained by first restricting M to
R[1/a] and then extending it to A with the direct coefficient extension of M
to A. It is an actual formal O-linear isomorphism with identity coordinate maps
in both directions. Equality of the addition and action series follows from
coefficient composition and `globalCoefficient_comp`.

`globalTransition` composes the a-chart comparison with the inverse b-chart
comparison. `ofGlobalCover M s hs` uses these actual isomorphisms and the
restricted global laws as its charts. Formal-map extensionality reduces the
identity transition, cocycle and coefficient-naturality equations to identities
of coordinate maps; composition and coefficient extension preserve the identity
coordinate map. Thus all three atlas requirements are proved from the global
law and coefficient maps rather than supplied as extra assumptions.

## Singleton comparison and its proof

`ofGlobal M` uses the singleton principal-open cover `{1}`. `oneChart` names its
chart and `oneChart_unit` proves that it is defined over every R-algebra A.
`globalPointEquiv M A` composes the previously proved local `chartEquiv` with
the point equivalence induced by `globalChartIso`. Its codomain is the actual
`M.AlgebraPoint A`, whose module operations are those of M extended to A.
Both inverse equations follow from the two constituent linear equivalences.

`globalPointEquiv_apply` proves that the forward map is evaluation of the
compatible family at the identity test A → A in its distinguished chart:
the final identity-coordinate formal map evaluates to the identity on tuples.
`globalPointEquiv_natural` compares this operation with coefficient extension.
The compatible family's naturality equation from the identity test along
A → B gives exactly the required equation, after removing the identity maps.

`globalPointFunctorIso` packages these equations as a natural isomorphism from
the singleton atlas point functor to `M.algebraPointFunctor` followed by
`ModuleCat.uliftFunctor`. The original module of nilpotent tuples lies in
universe v, while the product over all atlas tests lies in v+1. The component
is the proved linear equivalence followed by the inverse of
`ULift.moduleEquiv`; naturality is the preceding coefficient equation applied
under `ULift.up`. The lift changes the universe presentation of the module.
