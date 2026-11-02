# `Langlands.AnthropicFLT.P2M.Sol.S_IntermediateField_mem_adjoin_sum_mul_of_isSeparable_of_algebraicIndependent`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_IntermediateField_mem_adjoin_sum_mul_of_isSeparable_of_algebraicIndependent.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 1 `p2m_reactivate "N₁ N₂ …"` command(s) (an FLT command from `P2M.Util` that re-activates the scoped extensions, such as scoped instances and simp lemmas, of the named namespaces) are replaced by `open scoped _root_.N₁ _root_.N₂ …` with the same namespaces, which activates the same scoped extensions.
- Manual edit for Mathlib drift (FLT line 471, line 482 here): `have := congrArg (MvPolynomial.coeff m) hQzero` is replaced by `have := congrArg ((·.coeff m)) hQzero`. In the project's Mathlib, `MvPolynomial σ R` is the structure `AddMonoidAlgebra R (σ →₀ ℕ)` and the function `MvPolynomial.coeff m p` no longer exists; the coefficient of `p` at `m` is the field `p.coeff : (σ →₀ ℕ) →₀ R` applied to `m`, written `p.coeff m`. The FLT term `coeff m p` is rewritten accordingly; it denotes the same coefficient.
- Manual edit for Mathlib drift (FLT line 472, line 483 here): `rw [hQ, MvPolynomial.coeff_sum, MvPolynomial.coeff_zero] at this` is replaced by `rw [hQ, MvPolynomial.coeff_sum, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply] at this`. In the project's Mathlib, `MvPolynomial.coeff_zero` is a deprecated alias of `AddMonoidAlgebra.coeff_zero : (0 : R[M]).coeff = 0`, an equality of finitely supported functions; `Finsupp.coe_zero` and `Pi.zero_apply` evaluate it at the monomial, which gives the FLT rewrite.
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_IntermediateField_mem_adjoin_sum_mul_of_isSeparable_of_algebraicIndependent.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_IntermediateField_mem_adjoin_sum_mul_of_isSeparable_of_algebraicIndependent`. Statement. `IntermediateField.mem_adjoin_sum_mul_of_isSeparable_of_algebraicIndependent` (field-theoretic Bertini): let `K` be a
finitely generated field extension of an infinite field `k` in which `k` is separably closed, `g₀, …, g_n ∈ K` and
`c ∈ kⁿ⁺¹`, and let `x₀, …, x_n` be indeterminates over `K`. If `x`, `Σ gᵢ xᵢ` and `Σ cᵢ gᵢ` are algebraically
independent over `k`, then the field `k(x, Σ gᵢ xᵢ)` is separably closed in `K(x)`.

Proof. Sections `Transport`, `TransportSub`, `SC1`, `Permanence`: separable closedness (`SepClosedIn`) is transported
along field isomorphisms and is preserved under adjoining transcendental elements (`adjoin_transcendental`,
`sepClosedIn_adjoin_range`). Sections `FinSep`, `Bookkeeping`: a separable element over `k(x, Σ gᵢ xᵢ)` lies in a
finitely generated separable extension with bounded degree (`exists_bound_finrank_adjoin_of_fg`,
`exists_isSeparable_forall_mem_adjoin_of_fg`). Section `Omega`: it then lies in the adjunction of a single element
(`exists_ne_adjoin_simple_eq`). Section `ChangeVar`: changes of variables `σ`, `τ` (shifting `x` by multiples of `c`)
fix the subfield and are used to show the element is fixed by enough shifts (`mem_of_two_shifts`,
`transcendental_shift`). Section `Final` (`fieldBertini`): combining with separable closedness of `k` in `K`, the element
lies in `k(x, Σ gᵢ xᵢ)`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_IntermediateField_mem_adjoin_sum_mul_of_isSeparable_of_algebraicIndependent.P2mFieldBertini.isSeparable_transport`
- theorem `P2MW.S_IntermediateField_mem_adjoin_sum_mul_of_isSeparable_of_algebraicIndependent.P2mFieldBertini.isSeparable_of_le`
- theorem `P2MW.S_IntermediateField_mem_adjoin_sum_mul_of_isSeparable_of_algebraicIndependent.P2mFieldBertini.transcendental_of_le`
- theorem `P2MW.S_IntermediateField_mem_adjoin_sum_mul_of_isSeparable_of_algebraicIndependent.P2mFieldBertini.transcendental_of_le'`
- theorem `P2MW.S_IntermediateField_mem_adjoin_sum_mul_of_isSeparable_of_algebraicIndependent.P2mFieldBertini.restrictScalars_adjoin_eq`
- theorem `P2MW.S_IntermediateField_mem_adjoin_sum_mul_of_isSeparable_of_algebraicIndependent.P2mFieldBertini.separable_scaleRoots`
- theorem `P2MW.S_IntermediateField_mem_adjoin_sum_mul_of_isSeparable_of_algebraicIndependent.P2mFieldBertini.mem_adjoin_simple_of_isSeparable_of_transcendental`
- def `P2MW.S_IntermediateField_mem_adjoin_sum_mul_of_isSeparable_of_algebraicIndependent.P2mFieldBertini.SepClosedIn`
- theorem `P2MW.S_IntermediateField_mem_adjoin_sum_mul_of_isSeparable_of_algebraicIndependent.P2mFieldBertini.SepClosedIn.mono_right`
- theorem `P2MW.S_IntermediateField_mem_adjoin_sum_mul_of_isSeparable_of_algebraicIndependent.P2mFieldBertini.adjoin_coe_adjoin_union`
- theorem `P2MW.S_IntermediateField_mem_adjoin_sum_mul_of_isSeparable_of_algebraicIndependent.P2mFieldBertini.SepClosedIn.adjoin_transcendental`
- theorem `P2MW.S_IntermediateField_mem_adjoin_sum_mul_of_isSeparable_of_algebraicIndependent.P2mFieldBertini.SepClosedIn.adjoin_transcendental'`
- theorem `P2MW.S_IntermediateField_mem_adjoin_sum_mul_of_isSeparable_of_algebraicIndependent.P2mFieldBertini.isSeparable_of_isSeparable_bot`
- theorem `P2MW.S_IntermediateField_mem_adjoin_sum_mul_of_isSeparable_of_algebraicIndependent.P2mFieldBertini.sepClosedIn_adjoin_image`
- theorem `P2MW.S_IntermediateField_mem_adjoin_sum_mul_of_isSeparable_of_algebraicIndependent.P2mFieldBertini.sepClosedIn_adjoin_range`
- theorem `P2MW.S_IntermediateField_mem_adjoin_sum_mul_of_isSeparable_of_algebraicIndependent.P2mFieldBertini.linearIndependent_powerBasis_over_adjoin`
- theorem `P2MW.S_IntermediateField_mem_adjoin_sum_mul_of_isSeparable_of_algebraicIndependent.P2mFieldBertini.exists_bound_finrank_adjoin_of_fg`
- theorem `P2MW.S_IntermediateField_mem_adjoin_sum_mul_of_isSeparable_of_algebraicIndependent.P2mFieldBertini.exists_isSeparable_forall_mem_adjoin_of_fg`
- theorem `P2MW.S_IntermediateField_mem_adjoin_sum_mul_of_isSeparable_of_algebraicIndependent.P2mFieldBertini.exists_ne_adjoin_simple_eq`
- theorem `P2MW.S_IntermediateField_mem_adjoin_sum_mul_of_isSeparable_of_algebraicIndependent.P2mFieldBertini.map_adjoin_range_union_singleton`
- theorem `P2MW.S_IntermediateField_mem_adjoin_sum_mul_of_isSeparable_of_algebraicIndependent.P2mFieldBertini.fg_top_of_adjoin_eq_top`
- theorem `P2MW.S_IntermediateField_mem_adjoin_sum_mul_of_isSeparable_of_algebraicIndependent.P2mFieldBertini.mem_of_two_shifts`
- def `P2MW.S_IntermediateField_mem_adjoin_sum_mul_of_isSeparable_of_algebraicIndependent.P2mFieldBertini.tau`
- theorem `P2MW.S_IntermediateField_mem_adjoin_sum_mul_of_isSeparable_of_algebraicIndependent.P2mFieldBertini.tau_X`
- def `P2MW.S_IntermediateField_mem_adjoin_sum_mul_of_isSeparable_of_algebraicIndependent.P2mFieldBertini.sigma`
- theorem `P2MW.S_IntermediateField_mem_adjoin_sum_mul_of_isSeparable_of_algebraicIndependent.P2mFieldBertini.sigma_algebraMap`
- theorem `P2MW.S_IntermediateField_mem_adjoin_sum_mul_of_isSeparable_of_algebraicIndependent.P2mFieldBertini.sigma_X`
- theorem `P2MW.S_IntermediateField_mem_adjoin_sum_mul_of_isSeparable_of_algebraicIndependent.P2mFieldBertini.sigma_algebraMap_K`
- theorem `P2MW.S_IntermediateField_mem_adjoin_sum_mul_of_isSeparable_of_algebraicIndependent.P2mFieldBertini.adjoin_range_union_range_X_eq_top`
- theorem `P2MW.S_IntermediateField_mem_adjoin_sum_mul_of_isSeparable_of_algebraicIndependent.P2mFieldBertini.transcendental_shift`
- theorem `P2MW.S_IntermediateField_mem_adjoin_sum_mul_of_isSeparable_of_algebraicIndependent.P2mFieldBertini.transcendental_restrictScalars_adjoin`
- theorem `P2MW.S_IntermediateField_mem_adjoin_sum_mul_of_isSeparable_of_algebraicIndependent.P2mFieldBertini.fieldBertini`
- theorem `P2MW.S_IntermediateField_mem_adjoin_sum_mul_of_isSeparable_of_algebraicIndependent.solution`

## Dependencies

Ported FLT modules imported: none.
Other imports: `Mathlib`.
