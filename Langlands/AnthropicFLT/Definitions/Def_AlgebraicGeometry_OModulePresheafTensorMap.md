# `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafTensorMap`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Definition module (FLT `Definitions/`).

## Source and licence

Port of `Definitions/Def_AlgebraicGeometry_OModulePresheafTensorMap.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

For FLT presheaves of modules over `π : V ⟶ Spec R`, this module defines the tensor product of two morphisms,
for the sectionwise tensor product presheaf `F.tensor G` of the Library module
`Definitions.Def_AlgebraicGeometry_OModulePresheafTensor` (sections `F(U) ⊗_{Γ(V, U)} G(U)`):

- `Hom.tensorMap φ ψ : Hom (F.tensor G) (F'.tensor G')` for `φ : Hom F F'` and `ψ : Hom G G'`, given on each open
  `U` by `TensorProduct.map` of the section maps (`Hom.tensorMapApp`); it is natural because restriction of
  tensor products is computed on pure tensors.
- `AffHom.tensorMap φ ψ : AffHom (F.tensor G) (F'.tensor G')`, the same construction on affine opens for
  affine-indexed homomorphisms (`AffHom.tensorMapApp`).

The other declarations are lemmas: the evaluation lemmas `tensorMapApp_tmul`, `tensorMap_app_tmul`,
`tensorMap_app_apply` (for `Hom` and `AffHom`), extensionality `ext_app`, functoriality `tensorMap_id_id` and
`tensorMap_comp`, and `Hom.toAffHom_tensorMap` (the two constructions agree on affine opens).

## Declarations

Names, namespaces and statements are the FLT ones.

- def `AlgebraicGeometry.OModulePresheaf.Hom.tensorMapApp`
- theorem `AlgebraicGeometry.OModulePresheaf.Hom.tensorMapApp_tmul`
- def `AlgebraicGeometry.OModulePresheaf.Hom.tensorMap`
- theorem `AlgebraicGeometry.OModulePresheaf.Hom.tensorMap_app_tmul`
- theorem `AlgebraicGeometry.OModulePresheaf.Hom.tensorMap_app_apply`
- theorem `AlgebraicGeometry.OModulePresheaf.Hom.ext_app`
- theorem `AlgebraicGeometry.OModulePresheaf.Hom.tensorMap_id_id`
- theorem `AlgebraicGeometry.OModulePresheaf.Hom.tensorMap_comp`
- def `AlgebraicGeometry.OModulePresheaf.AffHom.tensorMapApp`
- theorem `AlgebraicGeometry.OModulePresheaf.AffHom.tensorMapApp_tmul`
- def `AlgebraicGeometry.OModulePresheaf.AffHom.tensorMap`
- theorem `AlgebraicGeometry.OModulePresheaf.AffHom.tensorMap_app_tmul`
- theorem `AlgebraicGeometry.OModulePresheaf.AffHom.tensorMap_app_apply`
- theorem `AlgebraicGeometry.OModulePresheaf.AffHom.ext_app`
- theorem `AlgebraicGeometry.OModulePresheaf.AffHom.tensorMap_id_id`
- theorem `AlgebraicGeometry.OModulePresheaf.AffHom.tensorMap_comp`
- theorem `AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_tensorMap`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafTensor` (Library).
Other imports: `Mathlib`.
