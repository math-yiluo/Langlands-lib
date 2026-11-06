# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_ker_eq_pow_smul_top_of_isClosedImmersion`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_ker_eq_pow_smul_top_of_isClosedImmersion.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_ker_eq_pow_smul_top_of_isClosedImmersion.solution`
proves the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_ker_eq_pow_smul_top_of_isClosedImmersion`.

Proof (namespace `P2mUnifGenAsm`). `q = ι ≫ π` is separated (`isSeparated`). `exists_compatible_lifts`: along an
inverse system of surjections, any finite family at level `0` lifts to a compatible family at all levels (recursive
choice of preimages). `main`: the ported theorem `exists_forall_exists_H0_tensor_twist_span_eq_top` (Serre's
theorem A for `F 0`) gives `d₁`, and the ported theorem
`exists_forall_surjective_H0Map_tensorMap_twist_of_forall_ker_eq_pow_smul_top` gives `d₀`; for `d = max d₀ d₁`
take generating cocycles `σ₀` of `F 0 ⊗ O(d)` and lift them compatibly through the surjective `H0` maps; the ported
theorem `exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top` then gives `E` and the
`θ k`. `solution` is `P2mUnifGenAsm.main`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_ker_eq_pow_smul_top_of_isClosedImmersion.P2mUnifGenAsm.isSeparated`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_ker_eq_pow_smul_top_of_isClosedImmersion.P2mUnifGenAsm.exists_compatible_lifts`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_ker_eq_pow_smul_top_of_isClosedImmersion.P2mUnifGenAsm.main`
- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_ker_eq_pow_smul_top_of_isClosedImmersion.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafTensorMap` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjTwistDatum` (Library), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_exists_H0_tensor_twist_span_eq_top` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_surjective_H0Map_tensorMap_twist_of_forall_ker_eq_pow_smul_top` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top` (same contribution).
Other imports: `Mathlib`.
