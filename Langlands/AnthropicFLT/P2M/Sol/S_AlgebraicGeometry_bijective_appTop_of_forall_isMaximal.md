# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_bijective_appTop_of_forall_isMaximal`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_bijective_appTop_of_forall_isMaximal.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_bijective_appTop_of_forall_isMaximal.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_bijective_appTop_of_forall_isMaximal`. Statement. `AlgebraicGeometry.bijective_appTop_of_forall_isMaximal`: for a quasi-compact, quasi-separated `q : X ⟶ Spec R`,
if for every maximal ideal `P` the base change of `q` to the localization `R_P` has bijective map on global
sections, then `q.appTop : R → Γ(X, ⊤)` is bijective.

Proof. Global sections commute with flat base change (ported
`isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat`), so the localization of `q.appTop` at each
maximal ideal is the map for the base change to `R_P` (`φ`, `ψ`, `γ`, `hw`); a linear map that is
bijective after localizing at all maximal ideals is bijective.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- def `P2MW.S_AlgebraicGeometry_bijective_appTop_of_forall_isMaximal.P2LocAux.φ`
- abbrev `P2MW.S_AlgebraicGeometry_bijective_appTop_of_forall_isMaximal.P2LocAux.A`
- abbrev `P2MW.S_AlgebraicGeometry_bijective_appTop_of_forall_isMaximal.P2LocAux.ι`
- abbrev `P2MW.S_AlgebraicGeometry_bijective_appTop_of_forall_isMaximal.P2LocAux.ΓP`
- def `P2MW.S_AlgebraicGeometry_bijective_appTop_of_forall_isMaximal.P2LocAux.ψ`
- def `P2MW.S_AlgebraicGeometry_bijective_appTop_of_forall_isMaximal.P2LocAux.γ`
- theorem `P2MW.S_AlgebraicGeometry_bijective_appTop_of_forall_isMaximal.P2LocAux.hw`
- theorem `P2MW.S_AlgebraicGeometry_bijective_appTop_of_forall_isMaximal.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat` (Library, ported by task `ab019f66-cba5-4921-aa53-b9cfb52e5456`).
Other imports: `Mathlib`.
