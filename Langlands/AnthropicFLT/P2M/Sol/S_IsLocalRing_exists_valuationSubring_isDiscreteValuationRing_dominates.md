# `Langlands.AnthropicFLT.P2M.Sol.S_IsLocalRing_exists_valuationSubring_isDiscreteValuationRing_dominates`

Ported for task `ab019f66-cba5-4921-aa53-b9cfb52e5456` (descent of geometric connectedness to finitely generated subalgebras). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_IsLocalRing_exists_valuationSubring_isDiscreteValuationRing_dominates.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

Proof (namespace `DvrDomination`).

- Step A (`exists_subalgebra_prime_height_le_one`): choose a valuation subring `V₀` of `K` dominating
  `R` (`LocalSubring.exists_le_valuationSubring`). Let `s` generate `𝔪_R` and `x ∈ s` maximize the
  `V₀`-valuation of the generators; `x ≠ 0` since `R` is not a field. The finitely generated (hence
  noetherian) subalgebra `S = R[s/x] ⊆ K` lies in `V₀`; the prime `𝔮 = 𝔪_{V₀} ∩ S` contains `x`;
  a minimal prime `P ⊆ 𝔮` over `(x)` has height `≤ 1` (Krull's principal ideal theorem), is nonzero,
  and satisfies `r ∈ 𝔪_R ↔ r ∈ P` for `r ∈ R` (since `𝔪_R S = x S ⊆ P` and `P ⊆ 𝔮` meets `R` in `𝔪_R`).
- Step B (`exists_dvr_of_height_le_one`): for a noetherian subring `S` of `K` with fraction field `K`
  and a nonzero prime `P` of height `≤ 1`, the localization `S_P` is a one-dimensional noetherian
  local domain; its integral closure `C` in `K` is noetherian of dimension `≤ 1`
  (`IsNoetherianRing.of_ringKrullDim_le_one_of_finiteDimensional_subalgebra`, Krull–Akizuki) and
  integrally closed, hence a Dedekind ring; localizing `C` at a maximal ideal over `P S_P` gives a
  discrete valuation ring `V ⊇ S` with `P = 𝔪_V ∩ S`. `dimensionLEOne_of_ringKrullDim_le_one`
  converts the Krull dimension bound to `Ring.DimensionLEOne`.
- `main` combines both steps; `solution` applies it.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_IsLocalRing_exists_valuationSubring_isDiscreteValuationRing_dominates.DvrDomination.dimensionLEOne_of_ringKrullDim_le_one`
- theorem `P2MW.S_IsLocalRing_exists_valuationSubring_isDiscreteValuationRing_dominates.DvrDomination.exists_dvr_of_height_le_one`
- theorem `P2MW.S_IsLocalRing_exists_valuationSubring_isDiscreteValuationRing_dominates.DvrDomination.exists_subalgebra_prime_height_le_one`
- theorem `P2MW.S_IsLocalRing_exists_valuationSubring_isDiscreteValuationRing_dominates.DvrDomination.main`
- theorem `P2MW.S_IsLocalRing_exists_valuationSubring_isDiscreteValuationRing_dominates.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Theorems.Thm_IsNoetherianRing_of_ringKrullDim_le_one_of_finiteDimensional_subalgebra` (same contribution).
All modules also import `Mathlib`.
