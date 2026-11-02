# `Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_HilbertFunctor_exists_forall_finrank_piece_eq_eval_of_isClosedImmersion_of_forall_mem_iff_of_eventually_eq`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AlgebraicGeometry_HilbertFunctor_exists_forall_finrank_piece_eq_eval_of_isClosedImmersion_of_forall_mem_iff_of_eventually_eq.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- Universe generalization. The FLT development works in universe 0 (`Type`, `Scheme.{0}`). For this project the ported files of the Hom-scheme construction are generalized to an arbitrary universe `uz`, so that the construction applies to abelian schemes over rings in any universe. Mechanical part in this file: a line `universe uz` is added (line 23 here); in 6 lines the replacements `Type` (universe 0) → `Type uz` (5 places), `Scheme.{0}` → `Scheme.{uz}` (1 place) are made, and these lines are otherwise unchanged. Consequently the statements become universe-polymorphic; the further changes are listed in the next item.
- Further changes (universe generalization): The local definitions `IsHilbPoly` (being the Hilbert polynomial of some homogeneous ideal over some field in universe `uz`) and `gnum` of this file depend on the universe `uz`, which does not occur in their arguments, so Lean cannot infer it at the use sites; the explicit universe argument `.{uz}` is added there (six lines). Nothing else changes in these lines. The changed lines are:
  - line 40 here:
    FLT text (universe-0 port):

    ```lean
    theorem exists_gotz (n : ℕ) (P : Polynomial ℚ) (hP : IsHilbPoly n P) :
    ```

    replacement:

    ```lean
    theorem exists_gotz (n : ℕ) (P : Polynomial ℚ) (hP : IsHilbPoly.{uz} n P) :
    ```
  - line 54 here:
    FLT text (universe-0 port):

    ```lean
      if h : IsHilbPoly n P then (exists_gotz n P h).choose else 0
    ```

    replacement:

    ```lean
      if h : IsHilbPoly.{uz} n P then (exists_gotz n P h).choose else 0
    ```
  - line 56 here:
    FLT text (universe-0 port):

    ```lean
    theorem gnum_eq (n : ℕ) (P : Polynomial ℚ) (h : IsHilbPoly n P) : gnum n P = (exists_gotz n P h).choose := by
    ```

    replacement:

    ```lean
    theorem gnum_eq (n : ℕ) (P : Polynomial ℚ) (h : IsHilbPoly.{uz} n P) : gnum.{uz} n P = (exists_gotz n P h).choose := by
    ```
  - line 113 here:
    FLT text (universe-0 port):

    ```lean
      refine ⟨max (gnum n P) (gnum n Q), ?_⟩
    ```

    replacement:

    ```lean
      refine ⟨max (gnum.{uz} n P) (gnum.{uz} n Q), ?_⟩
    ```
  - line 117 here:
    FLT text (universe-0 port):

    ```lean
      have hP : IsHilbPoly n P := ⟨k, inferInstance, I, hhom, D₁, hD₁⟩
    ```

    replacement:

    ```lean
      have hP : IsHilbPoly.{uz} n P := ⟨k, inferInstance, I, hhom, D₁, hD₁⟩
    ```
  - line 164 here:
    FLT text (universe-0 port):

    ```lean
      have hQ' : IsHilbPoly n Q := ⟨k, inferInstance, I ⊔ Ideal.span {ℓ}, hhom', D₁ + 1, hQev⟩
    ```

    replacement:

    ```lean
      have hQ' : IsHilbPoly.{uz} n Q := ⟨k, inferInstance, I ⊔ Ideal.span {ℓ}, hhom', D₁ + 1, hQev⟩
    ```
- No other change: apart from the edits listed above, the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_forall_finrank_piece_eq_eval_of_isClosedImmersion_of_forall_mem_iff_of_eventually_eq.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_HilbertFunctor_exists_forall_finrank_piece_eq_eval_of_isClosedImmersion_of_forall_mem_iff_of_eventually_eq`. Statement. `AlgebraicGeometry.HilbertFunctor.exists_forall_finrank_piece_eq_eval_of_isClosedImmersion_of_forall_mem_iff_of_eventually_eq`
(uniform regularity): for every `n` and `P ∈ ℚ[X]` there is `G` such that for every algebraically
closed field `k` (universe `uz`), every closed subscheme `Z_k ⊆ ℙⁿ_k` and every homogeneous ideal `I`
of `k[X₀, …, Xₙ]` whose forms are exactly those vanishing on `Z_k`: if `dim piece I d = P(d)` for all
large `d`, then this holds for all `d ≥ G`.

Proof (namespace `GotzReg`). `IsHilbPoly n P`: `P` is the Hilbert polynomial of some homogeneous ideal
over a field; `exists_gotz`: then there is `g ≥ 1` and a function `H` equal to `P` from `g` on which
grows maximally (`H (e + 1) = macaulayPow e (H e)`, the ported Gotzmann persistence data); `gnum` is
the chosen `g`. Take `G = max (gnum P) (gnum Q)` for `Q(X) = P(X) - P(X - 1)`. For `I` as in the
statement (saturated, as it is the ideal of `Z_k`), Macaulay's bound gives
`dim piece I e ≥ H e` (ported `MvPolynomial.le_finrank_piece_of_forall_succ_eq_macaulayPow_of_eventually_eq`).
A general linear form `ℓ` (exists since `k` is infinite) is a non-zero-divisor modulo `I`, so
`dim piece (I + (ℓ)) (e + 1) + dim piece I e = dim piece I (e + 1)` (ported
`MvPolynomial.finrank_piece_sup_span_singleton_succ_add_finrank_piece_eq_of_forall_mul_mem_imp`), and
`I + (ℓ)` has Hilbert polynomial `Q`. Applying Macaulay's bound to `I + (ℓ)` and descending induction
from the degrees where `I` agrees with `P` gives `dim piece I d = P(d)` for `d ≥ G`. (The annotations
`IsHilbPoly.{uz}` and `gnum.{uz}` are universe annotations; see the changes above.)

## Declarations

Names and namespaces are the FLT ones; statements are the FLT ones up to the changes listed above. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- def `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_forall_finrank_piece_eq_eval_of_isClosedImmersion_of_forall_mem_iff_of_eventually_eq.GotzReg.IsHilbPoly`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_forall_finrank_piece_eq_eval_of_isClosedImmersion_of_forall_mem_iff_of_eventually_eq.GotzReg.exists_gotz`
- def `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_forall_finrank_piece_eq_eval_of_isClosedImmersion_of_forall_mem_iff_of_eventually_eq.GotzReg.gnum`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_forall_finrank_piece_eq_eval_of_isClosedImmersion_of_forall_mem_iff_of_eventually_eq.GotzReg.gnum_eq`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_forall_finrank_piece_eq_eval_of_isClosedImmersion_of_forall_mem_iff_of_eventually_eq.GotzReg.isHomogeneous_of_forall`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_forall_finrank_piece_eq_eval_of_isClosedImmersion_of_forall_mem_iff_of_eventually_eq.GotzReg.forall_of_isHomogeneous`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_forall_finrank_piece_eq_eval_of_isClosedImmersion_of_forall_mem_iff_of_eventually_eq.GotzReg.homogeneous_sup_span_singleton`
- theorem `P2MW.S_AlgebraicGeometry_HilbertFunctor_exists_forall_finrank_piece_eq_eval_of_isClosedImmersion_of_forall_mem_iff_of_eventually_eq.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace` (Library), `Langlands.AnthropicFLT.Definitions.Def_AlgebraicGeometry_HilbertFunctor` (same contribution), `Langlands.AnthropicFLT.Definitions.Def_Nat_MacaulayPow` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_MvPolynomial_finrank_piece_succ_le_macaulayPow` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_Nat_exists_forall_eq_macaulayPow_of_forall_le_macaulayPow` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_MvPolynomial_le_finrank_piece_of_forall_succ_eq_macaulayPow_of_eventually_eq` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_MvPolynomial_finrank_piece_sup_span_singleton_succ_add_finrank_piece_eq_of_forall_mul_mem_imp` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_HilbertFunctor_mem_of_forall_exists_X_pow_mul_mem_of_forall_mem_iff_app_awayToSection_eq_zero` (same contribution), `Langlands.AnthropicFLT.Theorems.Thm_MvPolynomial_exists_forall_sum_C_mul_X_mul_mem_imp_of_forall_exists_X_pow_mul_mem` (same contribution).
Other imports: `Mathlib`.
