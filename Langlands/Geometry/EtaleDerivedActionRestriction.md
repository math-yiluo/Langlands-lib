# Group restriction of actual derived etale actions

This internal construction combines `EtaleDerivedEquivariantMap` with the
published `EtaleActionRestriction` and `EtalePullbackGroupRestriction`.
It derives the restriction comparison for actual derived actions from their
explicit action formula. It introduces no new source-backed comparison theorem.

Let `X : Scheme.{u}`, let `R : Type u` be a commutative ring, and let
`ρ : G →* (Aut X)ᵐᵒᵖ` describe an abstract group action. For any group
homomorphism `φ : H →* G`, the derived action of the restricted equivariant
coefficient sheaf acts at `h : H` by the original derived action at `φ h`.
The underlying derived object is unchanged. The two group universes and the
localization universes of the sheaf and module categories are independent.

`restrictionDerivedSectionsIso` uses the identity of that derived object.
The proved action formula makes this identity equivariant.
`restrictionDerivedSectionsFunctorIso` makes it natural in coefficient
morphisms: both underlying morphisms are the same derived-section map, so its
naturality square reduces to the identity laws. Both its forward and inverse
components have identity underlying derived maps.

For `q : ℕ`, `restriction_derivedHomology` states that this restriction
comparison commutes with canonical recovery of ordinary cohomology through
`pullbackDerivedHomologyFunctorIso` and the published ordinary group
restriction comparison. `restriction_derivedZero` gives the analogous square
with ordinary sections. The proofs forget the actions and use the identity
map under cohomology and the existing canonical comparison formulas.
These are equations between constructed equivariant maps; they do not use
faithfulness of cohomology.

For an equivariant etale map `f : Y ⟶ X` and an actual
`GeometricCoefficientMap`, `restrictGroup_derivedSectionsMap` compares the
derived map of the restricted coefficients with restriction of the derived
map. Both use the same geometric derived map followed by the same coefficient
morphism. `restrictionPullback_derivedSections` states this compatibility for
canonical geometric pullback, including the sheaf-level
`restrictionPullbackIso`. Its proof forgets the actions, uses the identity
underlying interchange map and the identity law for derived sections.
The two schemes may have independent sheaf localization universes.

All constructions use ordinary global sections of actual small-etale module
sheaves placed in degree zero, over a fixed scalar ring. The groups have no
topology, and the homomorphism need not be injective or surjective. Compact
supports, smoothness, scalar change, inverse limits and actual arithmetic or
Harris geometric specialization remain separate obligations.
