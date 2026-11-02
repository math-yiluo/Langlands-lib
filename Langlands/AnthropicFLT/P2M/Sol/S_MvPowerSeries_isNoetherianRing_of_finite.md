# `Langlands.AnthropicFLT.P2M.Sol.S_MvPowerSeries_isNoetherianRing_of_finite`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_MvPowerSeries_isNoetherianRing_of_finite.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

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

The theorem `P2MW.S_MvPowerSeries_isNoetherianRing_of_finite.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_MvPowerSeries_isNoetherianRing_of_finite`. Statement. `MvPowerSeries.isNoetherianRing_of_finite`: power series in finitely many variables over a noetherian ring form a
noetherian ring.

Proof. Section `Equiv`: power series in `Option σ` are power series in one variable over power series in `σ`
(`optFun`, `optInv`, `optRingEquiv`). Section `Noetherian`: induction on the number of variables using Mathlib's
noetherianity of `R⟦X⟧` for noetherian `R` (`isNoetherianRing_fin`), transported along `Fin n ≃ σ`
(`isNoetherianRing_of_finite`).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- def `P2MW.S_MvPowerSeries_isNoetherianRing_of_finite.M4cP1PS.optFun`
- def `P2MW.S_MvPowerSeries_isNoetherianRing_of_finite.M4cP1PS.optInv`
- theorem `P2MW.S_MvPowerSeries_isNoetherianRing_of_finite.M4cP1PS.coeff_coeff_optFun`
- theorem `P2MW.S_MvPowerSeries_isNoetherianRing_of_finite.M4cP1PS.coeff_optInv`
- theorem `P2MW.S_MvPowerSeries_isNoetherianRing_of_finite.M4cP1PS.optInv_optFun`
- theorem `P2MW.S_MvPowerSeries_isNoetherianRing_of_finite.M4cP1PS.optFun_optInv`
- theorem `P2MW.S_MvPowerSeries_isNoetherianRing_of_finite.M4cP1PS.optFun_add`
- theorem `P2MW.S_MvPowerSeries_isNoetherianRing_of_finite.M4cP1PS.optFun_mul`
- def `P2MW.S_MvPowerSeries_isNoetherianRing_of_finite.M4cP1PS.optRingEquiv`
- theorem `P2MW.S_MvPowerSeries_isNoetherianRing_of_finite.M4cP1PS.isNoetherianRing_fin`
- theorem `P2MW.S_MvPowerSeries_isNoetherianRing_of_finite.M4cP1PS.isNoetherianRing_of_finite`
- theorem `P2MW.S_MvPowerSeries_isNoetherianRing_of_finite.solution`

## Dependencies

Ported FLT modules imported: none.
Other imports: `Mathlib.RingTheory.PowerSeries.Ideal`, `Mathlib.RingTheory.MvPowerSeries.Rename`, `Mathlib.Data.Finsupp.Option`.
