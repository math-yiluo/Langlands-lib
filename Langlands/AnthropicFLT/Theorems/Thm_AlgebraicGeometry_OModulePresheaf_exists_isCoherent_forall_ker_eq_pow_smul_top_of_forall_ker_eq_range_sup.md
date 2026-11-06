# `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_forall_ker_eq_range_sup`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_forall_ker_eq_range_sup.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_forall_ker_eq_range_sup.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_forall_ker_eq_range_sup.solution I hHq hGc hGq h F φ ψ hψs hψk hψc`, the solution theorem applied to the explicit arguments of the theorem. The theorem statement is unchanged by this edit.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Statement. `AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_ker_eq_pow_smul_top_of_forall_ker_eq_range_sup`:
let `A` be a commutative ring, `I` an ideal, `q : P ⟶ Spec A`, `H` a quasi-coherent and `G` a coherent quasi-coherent
FLT presheaf over `q`, `h : AffHom H G`, and `F : ℕ → OModulePresheaf q` with maps `φ k : F (k+1) → F k`. Let
`ψ k : AffHom G (F k)` be surjective on affine opens with kernel `range h + I^(k+1) • ⊤` and compatible
(`φ k ∘ ψ (k+1) = ψ k`). Then the cokernel `G'` of `h` works: there are a coherent quasi-coherent `G'`, a map
`ρ : G → G'` surjective on affines with kernel the image of `h`, and maps `ψ' k : G' → F k` with
`ψ' k ∘ ρ = ψ k`, surjective on affines with kernel `I^(k+1) • ⊤`, and compatible (`φ k ∘ ψ' (k+1) = ψ' k`).
(If an adic system is presented as `G / (h(H) + I^(k+1) G)`, it is the adic system of the coherent sheaf
`coker h`.)

The proof term applies the companion solution theorem
`P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_forall_ker_eq_range_sup.solution`.

## Declarations

Names, namespaces and statements are the FLT ones.

- theorem `AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_ker_eq_pow_smul_top_of_forall_ker_eq_range_sup`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom` (Library), `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_forall_ker_eq_range_sup` (same contribution).
Other imports: `Mathlib`.
