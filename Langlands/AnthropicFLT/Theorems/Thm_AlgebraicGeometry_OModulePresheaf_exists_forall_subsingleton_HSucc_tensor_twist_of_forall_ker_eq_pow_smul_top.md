# `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_subsingleton_HSucc_tensor_twist_of_forall_ker_eq_pow_smul_top`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_subsingleton_HSucc_tensor_twist_of_forall_ker_eq_pow_smul_top.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_subsingleton_HSucc_tensor_twist_of_forall_ker_eq_pow_smul_top.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_subsingleton_HSucc_tensor_twist_of_forall_ker_eq_pow_smul_top.solution I ι hιq F hc hq φ hφs hφk K hKc hKq j hji hjr`, the solution theorem applied to the explicit arguments of the theorem. The theorem statement is unchanged by this edit.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Statement. `AlgebraicGeometry.OModulePresheaf.exists_forall_subsingleton_HSucc_tensor_twist_of_forall_ker_eq_pow_smul_top`:
let `A` be a noetherian commutative ring, `I` an ideal, `ι : P ⟶ ℙ^r_A` a closed immersion with
`q = ι ≫ ProjSpace.π A r`, `F : ℕ → OModulePresheaf q` coherent and quasi-coherent with maps
`φ k : AffHom (F (k+1)) (F k)` surjective on affine opens with kernel `I^(k+1) • ⊤`, and `K : ℕ → OModulePresheaf q`
coherent and quasi-coherent with `j k : AffHom (K k) (F (k+1))` injective on affine opens with image the kernel of
`φ k` (so `K k ≅ I^(k+1) F_{k+1}`). Then there is `d₀` such that for all `d ≥ d₀`, all `k` and all `i`, the Čech
cohomology `HSucc i` (`= H^(i+1)`) of `K k ⊗ O(d)` on the standard cover `ProjSpace.stdCoverPullback ι` vanishes.
(Serre vanishing uniform in `k`, the key input for lifting sections through the inverse system.)

The proof term applies the companion solution theorem
`P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_subsingleton_HSucc_tensor_twist_of_forall_ker_eq_pow_smul_top.solution`.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `AlgebraicGeometry.OModulePresheaf.exists_forall_subsingleton_HSucc_tensor_twist_of_forall_ker_eq_pow_smul_top`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafTensor` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjTwistDatum` (Library), `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_forall_subsingleton_HSucc_tensor_twist_of_forall_ker_eq_pow_smul_top` (same contribution).
Other imports: `Mathlib`.
