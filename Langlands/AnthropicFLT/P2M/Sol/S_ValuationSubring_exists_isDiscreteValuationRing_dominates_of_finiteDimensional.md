# `Langlands.AnthropicFLT.P2M.Sol.S_ValuationSubring_exists_isDiscreteValuationRing_dominates_of_finiteDimensional`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_ValuationSubring_exists_isDiscreteValuationRing_dominates_of_finiteDimensional.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- Manual edit for Mathlib drift: in the proof of `DvrExtFinite.main`, FLT line 96 `rw [← Ideal.mem_comap, hQ]; exact hx` is replaced by `rw [← Ideal.mem_comap, ← Ideal.under_def, hQ]; exact hx` (line 107 here). With the project's Mathlib the FLT rewrite fails: after `← Ideal.mem_comap` the goal is stated with `Ideal.comap (algebraMap ↥W ↥C) Q`, while `hQ` is stated with `Ideal.under ↥W Q`, and `rw` does not unfold the abbreviation `Ideal.under`. The inserted `← Ideal.under_def` (Mathlib `RingTheory/Ideal/Over.lean`, proved by `rfl`) restates the goal with `Ideal.under`. The proved statement `e2` is unchanged.
- No other change: the declarations and statements are the FLT text, and the proofs are the FLT text except for the edit above.

## Content

Proof (namespace `DvrExtFinite`).

- `dimensionLEOne_of_ringKrullDim_le_one`: a domain of Krull dimension `≤ 1` satisfies
  `Ring.DimensionLEOne`.
- `main`: the integral closure `C` of `W` in `E` is noetherian of dimension `≤ 1`
  (`IsNoetherianRing.of_ringKrullDim_le_one_of_finiteDimensional_subalgebra`, Krull–Akizuki), has
  fraction field `E`, and is integrally closed, hence a Dedekind domain. A maximal ideal `Q` of `C`
  over the maximal ideal of `W` (`Ideal.exists_ideal_over_maximal_of_isIntegral`) is nonzero, since
  `W` is not a field. The valuation subring `V` of `E` at `Q`
  (`IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime`) is the localization `C_Q`, a
  discrete valuation ring (`IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain`);
  it contains `C ⊇ W`, and elements of the maximal ideal of `W` lie in `Q`, hence are non-units of
  `V`.
- `solution` applies `main`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_ValuationSubring_exists_isDiscreteValuationRing_dominates_of_finiteDimensional.DvrExtFinite.dimensionLEOne_of_ringKrullDim_le_one`
- theorem `P2MW.S_ValuationSubring_exists_isDiscreteValuationRing_dominates_of_finiteDimensional.DvrExtFinite.main`
- theorem `P2MW.S_ValuationSubring_exists_isDiscreteValuationRing_dominates_of_finiteDimensional.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Theorems.Thm_IsNoetherianRing_of_ringKrullDim_le_one_of_finiteDimensional_subalgebra` (Library, ported by task `ab019f66-cba5-4921-aa53-b9cfb52e5456`).
All modules also import `Mathlib`.
