# `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafCechPushforward`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Definition module (FLT `Definitions/`).

## Source and licence

Port of `Definitions/Def_AlgebraicGeometry_OModulePresheafCechPushforward.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Let `p : V' ⟶ Z`, `πZ : Z ⟶ Spec R` and `K'` an ordered affine cover of `V'`. For an FLT presheaf of
modules `G` over `p ≫ πZ`, `OModulePresheaf.cechPushforward p πZ K' G` is an FLT presheaf of modules over
`πZ`, a Čech model of the pushforward of `G` along `p`:

- `cechPushforward.chart p K' U i := K'.U i ⊓ p ⁻¹ᵁ U` for an open `U` of `Z`.
- `cechPushforward.cocycles p πZ K' G U` is the `R`-submodule of families `x i : G(chart U i)` whose
  restrictions to `chart U i ⊓ chart U j` agree for all `i j` (`mem_cocycles_iff`); these are the
  sections of `cechPushforward p πZ K' G` over `U` (`cechPushforward_obj`).
- `Γ(Z, U)` acts componentwise through `toChart U i := p.appLE U (chart U i)` (`sectionsSMul`,
  `sectionsModule`); the restriction maps `resL` restrict each component (`res_mem` shows that cocycles
  restrict to cocycles).
- `Hom.cechPushforward` and `AffHom.cechPushforward` (the latter for `πZ` and `p` separated, using the
  affine charts `affineChart U i` of an affine open `U`) apply a morphism componentwise.

The other declarations are lemmas on these constructions: `chart_le_preimage`, `chart_mono`,
`toChart_algebraMap`, `map_toChart_left`, `map_toChart_right`, the unfolding lemmas `coe_res`, `coe_smul`,
`coe_sectionsSMul`, `coe_add`, the extensionality lemma `ext`, and `coe_cechPushforward_app` for
`Hom` and `AffHom`.

## Declarations

Names, namespaces and statements are the FLT ones.

- abbrev `AlgebraicGeometry.OModulePresheaf.cechPushforward.chart`
- theorem `AlgebraicGeometry.OModulePresheaf.cechPushforward.chart_le_preimage`
- theorem `AlgebraicGeometry.OModulePresheaf.cechPushforward.chart_mono`
- def `AlgebraicGeometry.OModulePresheaf.cechPushforward.cocycles`
- theorem `AlgebraicGeometry.OModulePresheaf.cechPushforward.mem_cocycles_iff`
- abbrev `AlgebraicGeometry.OModulePresheaf.cechPushforward.toChart`
- theorem `AlgebraicGeometry.OModulePresheaf.cechPushforward.toChart_algebraMap`
- theorem `AlgebraicGeometry.OModulePresheaf.cechPushforward.map_toChart_left`
- theorem `AlgebraicGeometry.OModulePresheaf.cechPushforward.map_toChart_right`
- def `AlgebraicGeometry.OModulePresheaf.cechPushforward.sectionsSMul`
- def `AlgebraicGeometry.OModulePresheaf.cechPushforward.sectionsModule`
- theorem `AlgebraicGeometry.OModulePresheaf.cechPushforward.res_mem`
- def `AlgebraicGeometry.OModulePresheaf.cechPushforward.resL`
- def `AlgebraicGeometry.OModulePresheaf.cechPushforward`
- theorem `AlgebraicGeometry.OModulePresheaf.cechPushforward_obj`
- theorem `AlgebraicGeometry.OModulePresheaf.cechPushforward.coe_res`
- theorem `AlgebraicGeometry.OModulePresheaf.cechPushforward.coe_smul`
- theorem `AlgebraicGeometry.OModulePresheaf.cechPushforward.coe_sectionsSMul`
- theorem `AlgebraicGeometry.OModulePresheaf.cechPushforward.coe_add`
- theorem `AlgebraicGeometry.OModulePresheaf.cechPushforward.ext`
- def `AlgebraicGeometry.OModulePresheaf.Hom.cechPushforward`
- theorem `AlgebraicGeometry.OModulePresheaf.Hom.coe_cechPushforward_app`
- abbrev `AlgebraicGeometry.OModulePresheaf.AffHom.affineChart`
- def `AlgebraicGeometry.OModulePresheaf.AffHom.cechPushforward`
- theorem `AlgebraicGeometry.OModulePresheaf.AffHom.coe_cechPushforward_app`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafLerayBicomplex` (Library).
Other imports: `Mathlib`.
