# Pullback on ordinary étale cohomology

For schemes `X` and `Y` in universe `u`, an étale morphism `f : Y ⟶ X`, and a
commutative ring `R : Type u`, this module constructs the natural maps

\[
H^q(X,F) \longrightarrow H^q(Y,f^*F), \qquad q\in\mathbb N.
\]

Here `F` is a sheaf of `ModuleCat.{u} R` on Mathlib's actual small étale site of
`X`. The notation `f^*` refers specifically to the published
`EtalePullback.restriction f (ModuleCat R)`: evaluation on an étale `Y`-scheme
uses its composite structure map to `X`. The cohomology functors are exactly
`EtaleDerivedSections.cohomology`, the right derived functors of the published
module-valued global-section functors. The construction is noncomputable and
uses their existing enough-injectives structure; neither cohomology objects nor
comparison maps are supplied as hypotheses.

## Exact restriction and resolutions

The published adjunctions establish the needed properties of restriction.
`EtalePullbackAdjunction` supplies its left adjoint, proves preservation of
limits, and proves preservation of injective objects. The independently
constructed right adjoint in `EtaleRestrictionRightAdjoint` supplies preservation
of colimits. Together with additivity, these yield the
`restriction_preservesHomology` instance.

`restrictedResolution f R I` applies the published
`DerivedComparison.mapInjectiveResolution` to an injective resolution `I` of
`F`. Its complex is the degreewise restriction of `I.cocomplex`, and its
augmentation is the restriction of the original augmentation, with the standard
single-complex identification. Exactness and injective preservation prove that
this is an injective resolution of `f^*F`.

For any such `I`, `restrictionDerivedIsoOfResolution` identifies
`R^q(f^* ⋙ Γ_Y)(F)` with `H^q(Y,f^*F)`. Both sides identify with the homology of
the same complex: apply `Γ_Y` to the restricted resolution. The comparison is
the forward resolution identification for the composite functor followed by
the inverse resolution identification for `Γ_Y`.

`restrictionDerivedIsoOfResolution_naturality` proves compatibility with a
coefficient morphism and any chain map between its source and target
resolutions that lifts that morphism in degree zero. It uses the two
naturality lemmas for `InjectiveResolution.isoRightDerivedObj` and the fact that
restriction carries the lift to a lift. Choosing the standard injective
resolutions and standard comparison lifts gives the natural isomorphism
`restrictionDerivedIso`.

## The cohomology map and its computation

`cohomologyMap f R q` first derives the already constructed natural section map
`sectionsMap f R : Γ_X ⟶ f^* ⋙ Γ_Y`, using `NatTrans.rightDerived`, and then
composes with `restrictionDerivedIso`. Its type is a natural transformation
from `cohomology X R q` to `restriction f (ModuleCat R) ⋙ cohomology Y R q`, so
naturality in the coefficient sheaf is part of the construction.

`resolutionSectionsMap f R I` applies `sectionsMap` in every degree of `I`.
`cohomologyMap_app` proves that on the chosen injective resolution the
cohomology map is the following composite:

1. Identify `H^q(X,F)` with the homology of `Γ_X(I)`.
2. Take homology of `resolutionSectionsMap`.
3. Use the inverse resolution identification for `Γ_Y(f^*I)`.

The proof expands the right-derived natural transformation using Mathlib's
resolution formula and cancels the intervening comparison isomorphisms.

`cohomologyMapWithCoefficients` further composes with the map on cohomology of a
specified morphism `α : f^*F ⟶ G` of sheaves on `Y`. It therefore has source
`H^q(X,F)` and target `H^q(Y,G)`. This is a change of coefficient *sheaf* over
the fixed ring `R`, not a construction of scalar extension to another ring.

## Degree zero

`resolutionSectionsMap_toRightDerivedZero'` proves compatibility of the section
chain map with the maps from sections to degree-zero cycles. The proof composes
with the monomorphism from cycles into the degree-zero term; the resulting
equality is naturality of `sectionsMap` for the resolution augmentation.

`cohomologyMap_toRightDerivedZero` then proves compatibility with the canonical
maps `Γ → R^0Γ`. It uses the resolution formula, naturality of the homology
projection, and the preceding equality on cycles. Finally,
`cohomologyMap_zero` proves that, under the published
`cohomologyZeroIso : H^0 ≅ Γ`, the constructed map is exactly `sectionsMap`.
The proof cancels the canonical isomorphism `Γ_X → R^0Γ_X` and uses the
compatibility just established.

## Provenance and scope

This is an internal construction from the published modules
`EtalePullback`, `EtalePullbackAdjunction`, `EtaleRestrictionRightAdjoint`,
`EtaleDerivedSections`, and `DerivedComparison`. Its right-derived-functor and
resolution operations come from pinned Mathlib
`CategoryTheory/Abelian/RightDerived.lean` (commit
`5ed2965256430c3649e86755f9576b54eca72435`). Its cycle and homology naturality
operations come from Mathlib's homological-complex interface. The arguments
above describe the implemented Lean proofs. No theorem from the original
Harris or Berkovich literature is asserted here.

The scope is ordinary module-valued cohomology on small étale sites and étale
scheme morphisms. Compatibility with scheme-morphism identities and
compositions in every degree is proved in
[`EtaleDerivedPullbackFunctoriality`](EtaleDerivedPullbackFunctoriality.md). General scheme
morphisms, analytic sites, compact support, smooth equivariant or Galois
actions, and specialization to Harris's spaces are likewise outside this
construction group and remain part of the broader framework work.
