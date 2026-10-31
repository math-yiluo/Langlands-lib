# `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat`

Ported for task `ab019f66-cba5-4921-aa53-b9cfb52e5456` (descent of geometric connectedness to finitely generated subalgebras). Statement module (FLT `Theorems/`).

## Source and licence

Port of `Theorems/Thm_AlgebraicGeometry_isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- The FLT proof `by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat.solution` (a tactic from `P2M.Util`) is replaced by the term `P2MW.S_AlgebraicGeometry_isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat.solution fX A`, the solution theorem applied to the explicit arguments of the theorem. The theorem statement is unchanged.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Flat base change of global sections. For a ring `k`, a quasi-compact quasi-separated scheme `X` with
a morphism `fX : X ⟶ Spec k`, and a flat `k`-algebra `A`, the square of commutative rings with
corners `k`, `Γ(X, ⊤)`, `A` and `Γ(X ×_k Spec A, ⊤)` (maps `algebraMap k A`, `fX.appTop` composed with
`Γ(Spec k) ≅ k`, and the maps on global sections of the two projections of the fibre product) is a
pushout in `CommRingCat`; that is, `Γ(X_A, 𝒪) ≅ Γ(X, 𝒪) ⊗_k A`. The proof term applies the
companion solution theorem.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `AlgebraicGeometry.isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat` (same contribution).
All modules also import `Mathlib`.
