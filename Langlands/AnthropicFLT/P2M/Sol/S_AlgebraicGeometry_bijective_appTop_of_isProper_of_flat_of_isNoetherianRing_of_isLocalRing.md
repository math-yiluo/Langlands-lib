# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isNoetherianRing_of_isLocalRing`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isNoetherianRing_of_isLocalRing.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 2 `p2m_reactivate "N₁ N₂ …"` command(s) (an FLT command from `P2M.Util` that re-activates the scoped extensions, such as scoped instances and simp lemmas, of the named namespaces) are replaced by `open scoped _root_.N₁ _root_.N₂ …` with the same namespaces, which activates the same scoped extensions.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isNoetherianRing_of_isLocalRing.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isNoetherianRing_of_isLocalRing`. Statement. `AlgebraicGeometry.bijective_appTop_of_isProper_of_flat_of_isNoetherianRing_of_isLocalRing`: the same statement for
a noetherian local ring `A` (not necessarily complete).

Proof. Pass to the completion `Â` (noetherian by the ported `AdicCompletion.isNoetherianRing_of_isNoetherianRing`,
local, complete, with the same residue field, `resMap`, `resIso`), which is faithfully flat over `A`. The base
change `X_Â` is proper and flat with the same closed fibre, so the complete case (ported
`bijective_appTop_of_isProper_of_flat_of_isAdicComplete`) applies, and faithfully flat descent of
bijectivity (as in `bijective_appTop_of_bijective_appTop_pullback_snd_of_faithfullyFlat`) concludes.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- lemma `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isNoetherianRing_of_isLocalRing.SolH0Nloc.bijective_of_isPushout_of_faithfullyFlat`
- abbrev `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isNoetherianRing_of_isLocalRing.SolH0Nloc.Ahat`
- anonymous instance of `IsNoetherianRing (Ahat A)`
- anonymous instance of `IsAdicComplete (IsLocalRing.maximalIdeal (Ahat A)) (Ahat A)`
- anonymous instance of `Module.FaithfullyFlat A (Ahat A)`
- def `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isNoetherianRing_of_isLocalRing.SolH0Nloc.resMap`
- lemma `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isNoetherianRing_of_isLocalRing.SolH0Nloc.resMap_bijective`
- def `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isNoetherianRing_of_isLocalRing.SolH0Nloc.resIso`
- lemma `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isNoetherianRing_of_isLocalRing.SolH0Nloc.quot_comp_resIso`
- lemma `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isNoetherianRing_of_isLocalRing.SolH0Nloc.appTop_bijective_of_isIso`
- lemma `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isNoetherianRing_of_isLocalRing.SolH0Nloc.appLE_top_top'`
- abbrev `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isNoetherianRing_of_isLocalRing.SolH0Nloc.jA`
- abbrev `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isNoetherianRing_of_isLocalRing.SolH0Nloc.Xh`
- abbrev `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isNoetherianRing_of_isLocalRing.SolH0Nloc.ph`
- abbrev `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isNoetherianRing_of_isLocalRing.SolH0Nloc.gh`
- anonymous instance of `IsProper (ph p)`
- anonymous instance of `Flat (jA (A`
- lemma `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isNoetherianRing_of_isLocalRing.SolH0Nloc.closedFibre_bijective`
- lemma `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isNoetherianRing_of_isLocalRing.SolH0Nloc.isPushout_appTop`
- lemma `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isNoetherianRing_of_isLocalRing.SolH0Nloc.jA_appTop_faithfullyFlat`
- theorem `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isNoetherianRing_of_isLocalRing.SolH0Nloc.main`
- theorem `P2MW.S_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isNoetherianRing_of_isLocalRing.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AdicCompletionLocalRing` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AdicCompletion_isNoetherianRing_of_isNoetherianRing` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_bijective_appTop_of_isProper_of_flat_of_isAdicComplete` (same contribution).
Other imports: `Mathlib`.
