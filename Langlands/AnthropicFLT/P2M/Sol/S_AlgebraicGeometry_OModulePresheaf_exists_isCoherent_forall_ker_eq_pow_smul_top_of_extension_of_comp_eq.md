# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_extension_of_comp_eq`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_extension_of_comp_eq.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_extension_of_comp_eq.solution`
proves the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_extension_of_comp_eq`.

Proof (direct, in `solution`): the given `G` and `ψ` work; only surjectivity and the kernel need proof, on a fixed
affine `U`.

- Surjectivity of `ψ k`: for `f ∈ F k(U)` pick `g₀ ∈ G(U)` with `ψE k (β g₀) = ε k f` (surjectivity of `β` and
  `ψE k`); then `f − ψ k g₀ ∈ ker (ε k) = range (lam k)`, say `= lam k y`, and `f = ψ k (g₀ + α y)` since
  `ψ k ∘ α = lam k`.
- Kernel: `I^(k+1)` kills `F k` (it is the image of `F (k+1)` with kernel `I^(k+1) • ⊤`), so `I^(k+1) G ⊆ ker ψ k`.
  Conversely, by induction on `c` the composite `Φ : F (k+c) → F k` of transition maps satisfies
  `Φ ∘ ψ (k+c) = ψ k` and `ker Φ = I^(k+1) • ⊤`. Choose `c` from `hlami` (`ker (lam (k+c)) ⊆ I^(k+1) GK`). For
  `g ∈ ker ψ k`: `ψ (k+c) g ∈ I^(k+1) F(k+c)`, so `g − x' ∈ ker ψ (k+c)` for some `x' ∈ I^(k+1) G`; then
  `β(g − x') ∈ ker ψE (k+c) = I^(k+c+1) GE`, so `g − x' − x'' ∈ ker β = range α` for some `x'' ∈ I^(k+c+1) G`, say
  `= α y`; as `ψ (k+c)` kills `x''`, `y ∈ ker lam (k+c) ⊆ I^(k+1) GK`, hence `α y ∈ I^(k+1) G`, and
  `g = x' + x'' + α y ∈ I^(k+1) G`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_extension_of_comp_eq.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafHom` (Library).
Other imports: `Mathlib`.
