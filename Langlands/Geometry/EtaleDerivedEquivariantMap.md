# Equivariant geometric maps on bounded-below derived etale sections

This internal construction lifts the published `GeometricCoefficientMap` and
equivariant pullback functor to actual group actions in D⁺. It uses
`EtaleDerivedAction` for the derived actions and `EtaleDerivedDiagram` for the
composition and equality-transport laws of geometric derived pullback.

Let `X` and `Y` be schemes in universe `u`, let `R : Type u` be a commutative
ring, and let a group `G : Type w` act through
`ρ : G →* (Aut X)ᵐᵒᵖ` and `τ : G →* (Aut Y)ᵐᵒᵖ`.
The etale morphism `f : Y ⟶ X` is equivariant: for every `g`, the two
composites `f ≫ (aut ρ g).hom` and `(aut τ g).hom ≫ f` agree.
The localizations of the two sheaf categories and the module category have
independent universes `wX`, `wY` and `wT`. The composition theorem allows a
third scheme with its own sheaf localization universe `wZ`.

For actual equivariant sheaves `F` and `E`, an input
`α : GeometricCoefficientMap R ρ τ f hf F E` consists of a coefficient
morphism `f*F.obj ⟶ E.obj` and its sheaf-level equivariance equation.
`α.derivedSectionsMap` has underlying morphism the actual geometric derived
pullback followed by derived sections of `α.hom`. To prove equivariance, expand
each group action, compose the two geometric derived maps, and use the
published `α.comp_coefficient` equation. Equality transport along the commuting
scheme square then gives the desired equality in D⁺. No equivariance of the
derived map is assumed, and equality on cohomology is not used to establish it.

The underlying-map theorem records this formula explicitly. The `precomp`
and `postcomp` theorems identify the derived maps obtained by composing the
coefficient input on either side with an equivariant coefficient morphism.
The source formula uses coefficient naturality of derived pullback; the
target formula uses functoriality of derived sections.

`derivedSectionsMap_homology` identifies the map obtained by applying degree
`q : ℕ` cohomology with the previously constructed equivariant ordinary
cohomology map, through the canonical action-valued comparison isomorphisms.
The proof forgets the actions and applies the proved ordinary recovery formula
for a derived map with target coefficients. The resulting equality is between
equivariant morphisms because those morphisms have already been constructed.
`derivedSectionsMap_zero` composes this comparison with the published
cohomology-to-sections comparison, recovering the geometric map on ordinary
sections with their actions.

Applying this construction to the identity coefficient map into the canonical
equivariant pullback defines `equivariantPullbackDerivedSections`, a natural
transformation on equivariant coefficient sheaves. Its coefficient naturality
is the naturality of the underlying derived pullback. Its underlying component
is exactly that geometric derived pullback, and the canonical homology
comparison identifies it with the existing equivariant cohomology pullback.
The degree-zero comparison likewise recovers equivariant restriction on
ordinary sections. Equality transport eliminates an equality of equivariant
scheme maps and simplifies the resulting identity coefficient comparison.
The identity and composition laws follow by forgetting the actions and using
the D⁺ identity/composition laws together with the published underlying
formulas for the equivariant coefficient-restriction comparisons.

All constructions use actual small-etale module sheaves and ordinary global
sections over a fixed scalar ring. The groups have no topology here.
Compact supports, smoothness, scalar change, inverse limits, arithmetic Galois
specialization and Harris-space realization remain separate constructions.
