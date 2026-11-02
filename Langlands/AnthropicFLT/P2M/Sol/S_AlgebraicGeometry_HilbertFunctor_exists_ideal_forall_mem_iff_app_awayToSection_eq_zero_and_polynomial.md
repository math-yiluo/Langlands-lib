# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_HilbertFunctor_exists_ideal_forall_mem_iff_app_awayToSection_eq_zero_and_polynomial`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_HilbertFunctor_exists_ideal_forall_mem_iff_app_awayToSection_eq_zero_and_polynomial.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- Universe generalization. The FLT development works in universe 0 (`Type`, `Scheme.{0}`). For this project the ported files of the Hom-scheme construction are generalized to an arbitrary universe `uz`, so that the construction applies to abelian schemes over rings in any universe. Mechanical part in this file: a line `universe uz` is added (line 20 here); in 4 lines the replacements `Type` (universe 0) → `Type uz` (2 places), `Scheme.{0}` → `Scheme.{uz}` (2 places) are made, and these lines are otherwise unchanged. Consequently the statements become universe-polymorphic; for `uz = 0` (and universe 0 for `Type*` binders) they are the FLT ones.
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_ideal_forall_mem_iff_app_awayToSection_eq_zero_and_polynomial.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_ideal_forall_mem_iff_app_awayToSection_eq_zero_and_polynomial`. Statement. `AlgebraicGeometry.HilbertFunctor.exists_ideal_forall_mem_iff_app_awayToSection_eq_zero_and_polynomial`:
for a closed subscheme `ιk : Z_k ⟶ ℙⁿ_k` over a field `k`, there is a homogeneous ideal `I` of
`k[X₀, …, Xₙ]` whose forms of each degree `d` are exactly the forms all of whose dehomogenizations
vanish on `Z_k`, and a polynomial `P ∈ ℚ[X]` with `dim_k piece I d = P(d)` for all large `d`.

Proof (namespace `E2SOL`). `frac i d F = F / Xᵢ^d` in the degree-zero localization (additive and
multiplicative, `frac_add`, `frac_mul`), `chartHom` its image on the chart `ιk⁻¹ D₊(Xᵢ)`, and
`Van d F`: all images vanish (closed under sums and multiplication by forms). `satIdeal ιk`: the
polynomials all of whose homogeneous components satisfy `Van`; it is an ideal (via
`homogeneousComponent_mul_of_mem_left`), homogeneous (`satIdeal_homogeneous`), with the required
description of its forms (`mem_satIdeal_iff_of_isHomogeneous`). Its Hilbert function satisfies
Macaulay's bound in degrees `≥ 1`, so it is eventually of maximal growth (ported
`Nat.exists_forall_eq_macaulayPow_of_forall_le_macaulayPow`) and then agrees with a polynomial (ported
`Nat.exists_polynomial_forall_eval_eq_of_forall_eq_macaulayPow`).

## Declarations

Names and namespaces are the FLT ones; statements are the FLT ones up to the changes listed above. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- def `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_ideal_forall_mem_iff_app_awayToSection_eq_zero_and_polynomial.E2SOL.xpow`
- def `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_ideal_forall_mem_iff_app_awayToSection_eq_zero_and_polynomial.E2SOL.frac`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_ideal_forall_mem_iff_app_awayToSection_eq_zero_and_polynomial.E2SOL.frac_zero`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_ideal_forall_mem_iff_app_awayToSection_eq_zero_and_polynomial.E2SOL.frac_add`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_ideal_forall_mem_iff_app_awayToSection_eq_zero_and_polynomial.E2SOL.frac_mul`
- def `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_ideal_forall_mem_iff_app_awayToSection_eq_zero_and_polynomial.E2SOL.chartHom`
- def `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_ideal_forall_mem_iff_app_awayToSection_eq_zero_and_polynomial.E2SOL.Van`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_ideal_forall_mem_iff_app_awayToSection_eq_zero_and_polynomial.E2SOL.Van_zero`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_ideal_forall_mem_iff_app_awayToSection_eq_zero_and_polynomial.E2SOL.Van_add`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_ideal_forall_mem_iff_app_awayToSection_eq_zero_and_polynomial.E2SOL.Van_mul_left`
- def `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_ideal_forall_mem_iff_app_awayToSection_eq_zero_and_polynomial.E2SOL.comp`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_ideal_forall_mem_iff_app_awayToSection_eq_zero_and_polynomial.E2SOL.comp_zero`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_ideal_forall_mem_iff_app_awayToSection_eq_zero_and_polynomial.E2SOL.comp_add`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_ideal_forall_mem_iff_app_awayToSection_eq_zero_and_polynomial.E2SOL.coe_decompose`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_ideal_forall_mem_iff_app_awayToSection_eq_zero_and_polynomial.E2SOL.homogeneousComponent_mul_of_mem_left`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_ideal_forall_mem_iff_app_awayToSection_eq_zero_and_polynomial.E2SOL.comp_of_mem`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_ideal_forall_mem_iff_app_awayToSection_eq_zero_and_polynomial.E2SOL.Van_comp_sum`
- def `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_ideal_forall_mem_iff_app_awayToSection_eq_zero_and_polynomial.E2SOL.satIdeal`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_ideal_forall_mem_iff_app_awayToSection_eq_zero_and_polynomial.E2SOL.mem_satIdeal_iff`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_ideal_forall_mem_iff_app_awayToSection_eq_zero_and_polynomial.E2SOL.satIdeal_homogeneous`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_ideal_forall_mem_iff_app_awayToSection_eq_zero_and_polynomial.E2SOL.mem_satIdeal_iff_of_isHomogeneous`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_ideal_forall_mem_iff_app_awayToSection_eq_zero_and_polynomial.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_HilbertFunctor` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_Nat_MacaulayPow` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_MvPolynomial_finrank_piece_succ_le_macaulayPow` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_Nat_exists_forall_eq_macaulayPow_of_forall_le_macaulayPow` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_Nat_exists_polynomial_forall_eval_eq_of_forall_eq_macaulayPow` (same contribution).
Other imports: `Mathlib`.
