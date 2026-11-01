# Global sections of trivial modules and of restriction units

Author: Worker 1119.

This helper module for the proof of
`Langlands.AlgebraicGeometry.Picard.FibreFrameLiftingStatement` computes the `T`-module
global sections (`DerivedSections.relativeGlobalSections`) of trivial modules over `Spec T`, and
proves two facts about the adjunction unit `M ⟶ j_* j^* M` of a morphism `j`. It contains no
`sorry` and no new axioms.

## Declarations

- `nonempty_relativeGlobalSections_unit_equiv`: for `h : Y ⟶ Spec T` with `h.appTop` an
  isomorphism, the `T`-module global sections of `𝒪_Y` are linearly equivalent to `T`. The
  module structure is restriction of scalars along `structureRingHom h`, which is bijective;
  the map `t ↦ t • 1` is therefore a bijective `T`-linear map `T ⟶ Γ(Y, ⊤)`.
- `nonempty_relativeGlobalSections_pushforward_equiv`: for `f' : X' ⟶ Spec T` and
  `g' : Y' ⟶ X'` with `(g' ≫ f').appTop` an isomorphism, and `W ≅ 𝒪_{Y'}`, the `T`-module
  global sections of `g'_* W` along `f'` are linearly equivalent to `T`. Proof: the Library's
  `relativeGlobalSectionsCompIso`, the isomorphism `W ≅ 𝒪`, and the previous item.
- `unitToPushforwardUnit_eq`: the structure comparison `𝒪_X ⟶ j_* 𝒪_Y` is the adjunction unit
  at `𝒪_X` followed by `j_*` of `pullbackUnitIso j`. This is the Library's
  `pullbackUnitAdjunction` rewritten with `Adjunction.homEquiv_unit`.
- `isIso_relativeGlobalSections_map_unit_unit`: if `f'.appTop` and `(j ≫ f').appTop` are
  isomorphisms, the global sections of the unit `𝒪_{X'} ⟶ j_* j^* 𝒪_{X'}` are bijective.
  Proof: `j.appTop` is an isomorphism (`Scheme.Hom.comp_appTop`). The global sections of
  `unitToPushforwardUnit j` are `j.appTop`, hence bijective. Cancel the isomorphism coming from
  `pullbackUnitIso j` using `unitToPushforwardUnit_eq`.
- `isIso_map_unit_app_of_iso`: for an adjunction `L ⊣ R`, a functor `F` and `θ : M ≅ O`, if
  `F` of the unit at `O` is an isomorphism then so is `F` of the unit at `M`. This uses
  naturality of the unit.
- `isIso_pullback_map_of_unit_app`: let `g : Y ⟶ X`, `ζ : g^* M ≅ 𝒪_Y` and
  `σ : 𝒪_X ⟶ M`. If the unit `M ⟶ g_* g^* M` sends the global section `σ(1)` to `ζ⁻¹(1)`,
  then `g^* σ` is an isomorphism, namely `pullbackUnitIso g ≫ ζ⁻¹`. Proof: the adjoint
  transposes of `g^* σ ≫ ζ` and of `pullbackUnitIso g` are `σ ≫ unit ≫ g_* ζ` and
  `unitToPushforwardUnit g` (`homEquiv_naturality_left`, `homEquiv_unit`,
  `pullbackUnitAdjunction`). Both are morphisms out of the structure module. By
  `sectionHomEquiv` they are equal once their values at `1` agree. Both values are `1`: the
  first by the hypothesis and `ζ ≫ ζ⁻¹ = 𝟙`, the second because `g.app ⊤` is a ring map.

## Provenance

Internal lemmas. They supply the degree-zero comparison of the proof of Stacks tag 0BF2
(`more-morphisms.tex`, lines 9543–9619, registered source
`stacks-picard-diagonal-seesaw-0bdp-0bf0-a04446e5`): `fₖ_* 𝒪 = 𝒪` universally, and the
passage from a degree-zero section of the model to an actual section `σ` of the line bundle.
