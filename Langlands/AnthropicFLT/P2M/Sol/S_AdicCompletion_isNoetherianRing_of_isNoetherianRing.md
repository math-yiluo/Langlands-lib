# `Langlands.AnthropicFLT.P2M.Sol.S_AdicCompletion_isNoetherianRing_of_isNoetherianRing`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AdicCompletion_isNoetherianRing_of_isNoetherianRing.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- Manual edit for Mathlib drift (FLT line 92, line 103 here): `fun x => ∑ j ∈ Finset.range (Finsupp.degree x + 1), MvPolynomial.coeff x (P j)` is replaced by `fun x => ∑ j ∈ Finset.range (Finsupp.degree x + 1), (P j).coeff x`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line 103, line 114 here): `change (∑ j ∈ Finset.range (Finsupp.degree x + 1), MvPolynomial.coeff x (P j)) = _` is replaced by `change (∑ j ∈ Finset.range (Finsupp.degree x + 1), (P j).coeff x) = _`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AdicCompletion_isNoetherianRing_of_isNoetherianRing.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AdicCompletion_isNoetherianRing_of_isNoetherianRing`. Statement. `AdicCompletion.isNoetherianRing_of_isNoetherianRing I`: for a noetherian ring `R` (in any universe
`u`) and an ideal `I`, the `I`-adic completion `AdicCompletion I R` is noetherian.

Proof (namespace `AdicCompletionNoetherian`). Choose generators `f₁, …, fₙ` of `I`. The evaluation
`ev : R[X₁, …, Xₙ] → R`, `Xᵢ ↦ fᵢ`, maps the ideal of the variables onto `I` and its powers onto the
powers of `I` (`map_XI_eq`, `map_XI_pow_eq`). Truncation of power series in total degree `< k`
followed by `ev` gives compatible maps `phi k : R⟦X₁, …, Xₙ⟧ → R ⧸ Iᵏ` (`phi_compat`), hence a ring
map `Phi : R⟦X₁, …, Xₙ⟧ → AdicCompletion I R` (`AdicCompletion.liftRingHom`), which is surjective
(`Phi_surjective`). The power series ring over a noetherian ring is noetherian
(`MvPowerSeries.isNoetherianRing_of_finite`), so its quotient `AdicCompletion I R` is noetherian.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- abbrev `P2MW.S_AdicCompletion_isNoetherianRing_of_isNoetherianRing.AdicCompletionNoetherian.XI`
- abbrev `P2MW.S_AdicCompletion_isNoetherianRing_of_isNoetherianRing.AdicCompletionNoetherian.ev`
- lemma `P2MW.S_AdicCompletion_isNoetherianRing_of_isNoetherianRing.AdicCompletionNoetherian.ev_C`
- lemma `P2MW.S_AdicCompletion_isNoetherianRing_of_isNoetherianRing.AdicCompletionNoetherian.ev_surjective`
- lemma `P2MW.S_AdicCompletion_isNoetherianRing_of_isNoetherianRing.AdicCompletionNoetherian.map_XI_eq`
- lemma `P2MW.S_AdicCompletion_isNoetherianRing_of_isNoetherianRing.AdicCompletionNoetherian.XI_le_comap`
- lemma `P2MW.S_AdicCompletion_isNoetherianRing_of_isNoetherianRing.AdicCompletionNoetherian.XI_pow_le_comap`
- lemma `P2MW.S_AdicCompletion_isNoetherianRing_of_isNoetherianRing.AdicCompletionNoetherian.map_XI_pow_eq`
- def `P2MW.S_AdicCompletion_isNoetherianRing_of_isNoetherianRing.AdicCompletionNoetherian.phi`
- lemma `P2MW.S_AdicCompletion_isNoetherianRing_of_isNoetherianRing.AdicCompletionNoetherian.phi_apply`
- lemma `P2MW.S_AdicCompletion_isNoetherianRing_of_isNoetherianRing.AdicCompletionNoetherian.phi_eq_of_sub_mem`
- lemma `P2MW.S_AdicCompletion_isNoetherianRing_of_isNoetherianRing.AdicCompletionNoetherian.phi_compat`
- def `P2MW.S_AdicCompletion_isNoetherianRing_of_isNoetherianRing.AdicCompletionNoetherian.Phi`
- lemma `P2MW.S_AdicCompletion_isNoetherianRing_of_isNoetherianRing.AdicCompletionNoetherian.evalₐ_Phi`
- lemma `P2MW.S_AdicCompletion_isNoetherianRing_of_isNoetherianRing.AdicCompletionNoetherian.Phi_surjective`
- theorem `P2MW.S_AdicCompletion_isNoetherianRing_of_isNoetherianRing.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Theorems.Thm_MvPowerSeries_isNoetherianRing_of_finite` (same contribution).
Other imports: `Mathlib`.
