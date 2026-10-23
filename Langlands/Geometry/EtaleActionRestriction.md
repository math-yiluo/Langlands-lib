# Restriction of equivariant étale coefficients along group homomorphisms

This module constructs group restriction for the existing category of actual
translation-equivariant small-étale module sheaves. It identifies the resulting
ordinary cohomology and section actions with restriction of the original actions,
naturally in the coefficient sheaf and compatibly with the canonical degree-zero
comparison.

Fix a scheme `Y : Scheme.{u}`, a commutative ring `R : Type u`, independently
universe-polymorphic groups `G : Type w` and `H : Type w'`, a homomorphism
`ρ : G →* (Aut Y)ᵐᵒᵖ`, and `φ : H →* G`. No topology or injectivity condition on
`φ` is required. Coefficients are sheaves of `ModuleCat.{u} R` on the actual small
étale site of `Y`. Write `σ_g = aut ρ g`. The existing convention is
`σ_(g*h) = σ_g ≪≫ σ_h`; an equivariant coefficient sheaf has maps
`F.act g : translateBy R ρ g (F.obj) ⟶ F.obj` satisfying the existing translation
unit and product laws.

## Reconstruction and restriction

`toEquivariant` reconstructs an equivariant sheaf from a `CoefficientDiagram`
on `actionSchemeDiagram ρ`: it takes the sheaf at `SingleObj.star G` and uses
`D.map g` as the structure map. The previously proved identity and composition
constraint comparisons convert the diagram laws to the translation cocycle laws.
For the product law, the equation for arrows `h` then `g` is used, since their
composite in `SingleObj G` is `g*h`. Composing with the inverse constraint gives
the required formula. `toEquivariantFunctor` evaluates a coefficient-diagram
morphism at the sole vertex; its compatibility, identity and composition laws
are inherited from the diagram morphism laws.

`actionSchemeDiagram_comp` states the definitional equality between precomposing
`actionSchemeDiagram ρ` with `SingleObj.mapHom H G φ` and the diagram of `ρ.comp φ`.
`restrictionFunctor R ρ φ` is the composite of the existing conversion
`ofEquivariantFunctor`, the existing `CoefficientDiagram.reindexFunctor` along
that index functor, and `toEquivariantFunctor`. Consequently it retains `F.obj`,
replaces `F.act h` by `F.act (φ h)`, and retains the underlying morphism `f.hom`.
The three displayed formulas in Lean are definitional equalities. Restriction is
faithful because equality of its underlying coefficient morphisms implies
equality of the original equivariant morphisms.

`restrictionIdIso` identifies restriction along `MonoidHom.id G` with the
identity functor. For a further group `K : Type w''` and `ψ : K →* H`,
`restrictionCompIso` identifies restriction along `φ` followed by restriction
along `ψ` with restriction along `φ.comp ψ`. Both have identity underlying
sheaf maps. Equivariance follows from the evaluation formula for the structure
maps; naturality follows from the unchanged underlying coefficient morphisms.
The module does not bundle these isomorphisms into a pseudofunctor.

## Cohomology and sections

For every `q : ℕ`, `restriction_cohomology_ρ` proves that `h : H` acts on
cohomology of the restricted sheaf by exactly the original action of `φ h`.
The proof uses the established geometric formula
`cohomologyMapWithCoefficients σ_g.hom R q (F.act g)` on both sides. The
underlying module is the existing ordinary right-derived global-section module
`(EtaleDerivedSections.cohomology Y R q).obj F.obj`.

`restrictionCohomologyIso` packages that equality as an isomorphism of `H`
actions with identity underlying module map. `restrictionCohomologyFunctorIso`
then identifies the functors

```
restrictionFunctor R ρ φ ⋙ pullbackCohomologyFunctor R (ρ.comp φ) q
  ≅ pullbackCohomologyFunctor R ρ q ⋙ Action.res (ModuleCat R) φ.
```

Its naturality reduces to the ordinary cohomology map of `f.hom` composed with
an identity on either side. The accompanying component lemma states that its
underlying forward map is the identity on the explicitly named ordinary
cohomology module. Its proof uses the component of the objectwise isomorphism
and `Action.mkIso_hom_hom`, avoiding deep definitional unfolding of the
cohomology action.

`restriction_sections_ρ` is the analogous evaluation formula for global section
actions; here it holds definitionally. `restrictionSectionsIso` and
`restrictionSectionsFunctorIso` give the objectwise and coefficient-natural
comparisons with `Action.res`, again with identity underlying maps. The section
naturality proof uses the published `pullbackSectionsFunctor_map_hom` formula to
identify both coefficient maps with ordinary sections of `f.hom`.

Finally, `restriction_cohomologyZero` proves the commutative square of `H`-action
morphisms: first compare restricted cohomology with restriction of cohomology
and then restrict the canonical degree-zero comparison, or first apply the
canonical degree-zero comparison to the restricted sheaf and then compare
sections. After forgetting actions, both composites are exactly the canonical
ordinary map `(EtaleDerivedSections.cohomologyZeroIso Y R).hom.app F.obj`.

## Provenance and scope

This is internal categorical infrastructure derived from `EtaleActionFunctor`,
`EtaleActionDiagram`, `EtaleCohomologyReindex`, and the translation-equivariant
morphism category. Mathlib supplies `SingleObj.mapHom`, `Action.res`, and the
isomorphism constructors. All restriction, equivariance and naturality fields
are proved from the existing sheaf cocycle and geometric cohomology formulas;
no cohomology compatibility is assumed as additional input.

The scheme and its action are supplied. This module does not construct Harris
level schemes, compact-support cohomology, a smooth or continuous action,
coefficient scalar change, inverse-limit comparisons, or derived functors in
the equivariant category. Its all-degree result concerns the existing ordinary
small-étale cohomology equipped with its geometric action.
