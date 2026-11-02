# `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafTensor`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Definition module (FLT `Definitions/`).

## Source and licence

Port of `Definitions/Def_AlgebraicGeometry_OModulePresheafTensor.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Tensor products of FLT's `OModulePresheaf π` (namespace `AlgebraicGeometry.OModulePresheaf`), for
`π : V ⟶ Spec R`.

- `tensorObjModule F G U` (reducible): the `R`-module structure on `F(U) ⊗_{Γ(V,U)} G(U)` by
  restriction of scalars along `R → Γ(V, U)`.
- `tensorResₛₗ F G h`: for `U ≤ U'`, the map `F(U') ⊗ G(U') → F(U) ⊗ G(U)`, `x ⊗ y ↦ x|_U ⊗ y|_U`,
  semilinear over the restriction `Γ(V, U') → Γ(V, U)`; `tensorResₛₗ_tmul` is its value on pure
  tensors. `tensorRes F G h` is the same map as an `R`-linear map.
- `tensor F G`: the presheaf `U ↦ F(U) ⊗_{Γ(V,U)} G(U)` with these restriction maps (the identity and
  composition laws are checked on pure tensors). `tensor_obj`, `tensor_res_tmul`,
  `tensor_res_apply`, `tensor_smul_tmul` and `tensor_algebraMap_smul` unfold it.
- Section `Twist`: `twist F L = F.tensor (ofModules π L)` for a sheaf of modules `L` on `V`, with
  `twist_obj` and `twist_res_tmul`.

## Declarations

Names, namespaces and statements are the FLT ones.

- def `AlgebraicGeometry.OModulePresheaf.tensorObjModule`
- def `AlgebraicGeometry.OModulePresheaf.tensorResₛₗ`
- theorem `AlgebraicGeometry.OModulePresheaf.tensorResₛₗ_tmul`
- def `AlgebraicGeometry.OModulePresheaf.tensorRes`
- def `AlgebraicGeometry.OModulePresheaf.tensor`
- theorem `AlgebraicGeometry.OModulePresheaf.tensor_obj`
- theorem `AlgebraicGeometry.OModulePresheaf.tensor_res_tmul`
- theorem `AlgebraicGeometry.OModulePresheaf.tensor_res_apply`
- theorem `AlgebraicGeometry.OModulePresheaf.tensor_smul_tmul`
- theorem `AlgebraicGeometry.OModulePresheaf.tensor_algebraMap_smul`
- abbrev `AlgebraicGeometry.OModulePresheaf.twist`
- theorem `AlgebraicGeometry.OModulePresheaf.twist_obj`
- theorem `AlgebraicGeometry.OModulePresheaf.twist_res_tmul`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules` (Library).
Other imports: `Mathlib.LinearAlgebra.TensorProduct.Basic`.
