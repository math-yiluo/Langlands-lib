# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_geometricallyConnected_of_isProper_of_flat_of_bijective_appTop_pullback_snd`

Ported for task `ab019f66-cba5-4921-aa53-b9cfb52e5456` (descent of geometric connectedness to finitely generated subalgebras). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_geometricallyConnected_of_isProper_of_flat_of_bijective_appTop_pullback_snd.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 2 `p2m_reactivate "N₁ N₂ …"` command(s) (an FLT command from `P2M.Util` that re-activates the scoped extensions, such as scoped instances and simp lemmas, of the named namespaces) are replaced by `open scoped _root_.N₁ _root_.N₂ …` with the same namespaces, which activates the same scoped extensions.
- No other change: the declarations, statements and proofs are the FLT text. The FLT `attribute [-…]`
  lines after the namespace header (which locally deactivate instances and simp lemmas declared in
  imported FLT modules) are kept unchanged.

## Content

Proof (namespace `R4ZconnH0`, inside a `noncomputable section`). Reduce to
`geometricallyConnected_of_isProper_of_bijective_appTop` by showing that `f.appTop` is bijective.
`Spec K ⟶ Spec R` is dominant and scheme-theoretically dominant (scoped instances), so its base
change `g : X_K ⟶ X` along the flat `f` is scheme-theoretically dominant and `g.appTop` is
injective. In the square `R → Γ(X)`, `K → Γ(X_K)`, `Γ(X) → Γ(X_K)`, the map `R → Γ(X)` is integral
(`f` universally closed, `isIntegral_appTop_of_universallyClosed`) and `K → Γ(X_K)` is bijective
by hypothesis; since `R` is integrally closed, `R → Γ(X)` is bijective (`bijective_of_square`:
injectivity through `K`, and every section is integral over `R` with image in `K`, hence comes from
`R`).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- lemma `P2MW.S_AlgebraicGeometry_geometricallyConnected_of_isProper_of_flat_of_bijective_appTop_pullback_snd.R4ZconnH0.bijective_of_square`
- abbrev `P2MW.S_AlgebraicGeometry_geometricallyConnected_of_isProper_of_flat_of_bijective_appTop_pullback_snd.R4ZconnH0.ι`
- scoped instance `P2MW.S_AlgebraicGeometry_geometricallyConnected_of_isProper_of_flat_of_bijective_appTop_pullback_snd.R4ZconnH0.isDominant_ι`
- scoped instance `P2MW.S_AlgebraicGeometry_geometricallyConnected_of_isProper_of_flat_of_bijective_appTop_pullback_snd.R4ZconnH0.isSchemeTheoreticallyDominant_ι`
- theorem `P2MW.S_AlgebraicGeometry_geometricallyConnected_of_isProper_of_flat_of_bijective_appTop_pullback_snd.R4ZconnH0.bijective_appTop`
- theorem `P2MW.S_AlgebraicGeometry_geometricallyConnected_of_isProper_of_flat_of_bijective_appTop_pullback_snd.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_geometricallyConnected_of_isProper_of_bijective_appTop` (same contribution).
All modules also import `Mathlib`.
