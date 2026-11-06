# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_forall_surjective_H0Map_tensorMap_twist_of_forall_ker_eq_pow_smul_top`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_forall_surjective_H0Map_tensorMap_twist_of_forall_ker_eq_pow_smul_top.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_surjective_H0Map_tensorMap_twist_of_forall_ker_eq_pow_smul_top.solution`
proves the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_surjective_H0Map_tensorMap_twist_of_forall_ker_eq_pow_smul_top`.

Proof (namespace `P2mUnifLift`). `q` is locally of finite type (it factors through the closed immersion `ι` into
`ℙ^r_A`; `locallyOfFiniteType`), so `P` is locally noetherian. Two affine homomorphisms out of a tensor product
agreeing on pure tensors are equal (`affHom_tensor_ext`). `main`: the ported theorem
`AffHom.exists_isQuasicoherent_injective_range_eq_ker` gives quasi-coherent (hence coherent) kernels
`j k : K k → F (k+1)` of the `φ k`; the ported theorem
`exists_forall_subsingleton_HSucc_tensor_twist_of_forall_ker_eq_pow_smul_top` gives `d₀` with
`H^1(K k ⊗ O(d)) = 0` for `d ≥ d₀` and all `k`. For such `d` and `k`, tensoring the short exact sequence
`0 → K k → F (k+1) → F k → 0` with the flat twist `O(d)` (Library theorems `ProjSpace.isCoherent_twist_and_flat`,
`exists_affSES_tensor_of_flat`) gives a short exact sequence whose projection is `φ k ⊗ id`; the Library connecting
homomorphism `AffSES.exists_connectingHom` has kernel the image of `H0` of the projection, and it lands in
`H^1(K k ⊗ O(d)) = 0`, so `H0Map` of `φ k ⊗ id` is surjective. `solution` is `P2mUnifLift.main`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_surjective_H0Map_tensorMap_twist_of_forall_ker_eq_pow_smul_top.P2mUnifLift.locallyOfFiniteType`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_surjective_H0Map_tensorMap_twist_of_forall_ker_eq_pow_smul_top.P2mUnifLift.affHom_tensor_ext`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_surjective_H0Map_tensorMap_twist_of_forall_ker_eq_pow_smul_top.P2mUnifLift.main`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_surjective_H0Map_tensorMap_twist_of_forall_ker_eq_pow_smul_top.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafTensorMap` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjTwistDatum` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_subsingleton_HSucc_tensor_twist_of_forall_ker_eq_pow_smul_top` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_ProjSpace_isCoherent_twist_and_flat` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_affSES_tensor_of_flat` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_AffSES_exists_connectingHom` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_AffHom_exists_isQuasicoherent_injective_range_eq_ker` (same contribution).
Other imports: `Mathlib`.
