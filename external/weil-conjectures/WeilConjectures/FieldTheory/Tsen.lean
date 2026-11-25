/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import WeilConjectures.FieldTheory.Cr
public import WeilConjectures.Mathlib.RingTheory.MvPolynomial.Localization
public import WeilConjectures.Mathlib.RingTheory.Nullstellensatz

/-!
# Tsen's theorem

A field of transcendence degree at most one over an algebraically closed field `k` is
quasi-algebraically closed (`C₁`).

## Main statements

- `RatFunc.isQuasiAlgClosed`: the rational function field `k(t)` is `C₁`.
- `IsQuasiAlgClosed.of_trdeg_le_one`: **Tsen's theorem**.

## Implementation notes

For `k(t)` we follow Lang: a form `F` of degree `d` in `N > d` variables with coefficients in
`k[t]` of degree at most `r` is evaluated on `N`-tuples of polynomials of degree at most `m`.
The vanishing of `F(x(t))` amounts to `d m + r + 1` equations without constant term in the
`N (m + 1)` coefficients of `x(t)`, which have a common nontrivial zero over `k` as soon as
`N (m + 1) > d m + r + 1` (`MvPolynomial.exists_ne_zero_forall_eval_eq_zero`).
-/

@[expose] public section

open MvPolynomial

namespace MvPolynomial

/-- The degree in `t` of `G(x(t))`, for a form `G` of degree `d` whose coefficients have degree at
most `r` and polynomials `x i` of degree at most `m`, is at most `d * m + r`. -/
lemma natDegree_eval_le_of_isHomogeneous {R σ : Type*} [CommRing R] [Finite σ]
    {G : MvPolynomial σ (Polynomial R)} {d r m : ℕ} (hG : G.IsHomogeneous d)
    (hr : ∀ s, (G.coeff s).natDegree ≤ r) {x : σ → Polynomial R}
    (hx : ∀ i, (x i).natDegree ≤ m) : (eval x G).natDegree ≤ d * m + r := by
  have := Fintype.ofFinite σ
  rw [eval_eq']
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun s hs ↦ ?_
  refine (Polynomial.natDegree_mul_le).trans ?_
  rw [add_comm]
  gcongr
  · refine (Polynomial.natDegree_prod_le _ _).trans ?_
    have hs' : ∑ i, s i = d := by
      rw [← hG (mem_support_iff.mp hs), Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
      simp
    rw [← hs', Finset.sum_mul]
    exact Finset.sum_le_sum fun i _ ↦
      Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left _ (hx i))
  · exact hr s

/-- Substituting polynomials with indeterminate coefficients commutes with specialising these
coefficients: `y ↦ G(Σⱼ yᵢⱼ tʲ)` is computed coefficientwise by the generic substitution. -/
lemma map_eval_eval₂_sum_C_mul_X_pow {R σ ι : Type*} [CommRing R] [Fintype ι] (e : ι → ℕ)
    (G : MvPolynomial σ (Polynomial R)) (y : σ × ι → R) :
    (eval₂ (Polynomial.mapRingHom (algebraMap R (MvPolynomial (σ × ι) R)))
        (fun i ↦ ∑ j, Polynomial.C (X (i, j)) * Polynomial.X ^ e j) G).map (eval y) =
      eval (fun i ↦ ∑ j, Polynomial.C (y (i, j)) * Polynomial.X ^ e j) G := by
  rw [← Polynomial.coe_mapRingHom, eval₂_comp_left, Polynomial.mapRingHom_comp]
  have h : (eval y).comp (algebraMap R (MvPolynomial (σ × ι) R)) = RingHom.id R := by
    ext
    simp
  rw [h, Polynomial.mapRingHom_id, eval]
  congr 1
  ext i : 1
  simp [Polynomial.map_sum]

/-- **Tsen's theorem over `k[t]`** (Lang's argument). Over an algebraically closed field `k`, a
form of degree `d > 0` in more than `d` variables with coefficients in `k[t]` has a nontrivial
zero in `k[t]`: the coefficients of `G(x(t))` for `x(t)` of degree at most `r` are `d r + r + 1`
equations without constant term in the `N (r + 1)` coefficients of `x(t)`. -/
theorem exists_ne_zero_eval_eq_zero_of_isHomogeneous_polynomial {k σ : Type*} [Field k]
    [IsAlgClosed k] [Finite σ] {d : ℕ} (G : MvPolynomial σ (Polynomial k))
    (hG : G.IsHomogeneous d) (hd : 0 < d) (hσ : d < Nat.card σ) :
    ∃ x : σ → Polynomial k, x ≠ 0 ∧ eval x G = 0 := by
  have := Fintype.ofFinite σ
  set r := G.support.sup fun s ↦ (G.coeff s).natDegree
  have hr (s : σ →₀ ℕ) : (G.coeff s).natDegree ≤ r := by
    by_cases hs : s ∈ G.support
    · exact Finset.le_sup (f := fun s ↦ (G.coeff s).natDegree) hs
    · simp [notMem_support_iff.mp hs]
  have hx (y : σ × Fin (r + 1) → k) (i : σ) :
      (∑ j : Fin (r + 1), Polynomial.C (y (i, j)) * Polynomial.X ^ (j : ℕ)).natDegree ≤ r :=
    Polynomial.natDegree_sum_le_of_forall_le _ _ fun j _ ↦
      (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.mp j.2)
  set Φ := eval₂ (Polynomial.mapRingHom (algebraMap k (MvPolynomial (σ × Fin (r + 1)) k)))
    (fun i ↦ ∑ j : Fin (r + 1), Polynomial.C (X (i, j)) * Polynomial.X ^ (j : ℕ)) G
  have hΦ (l : ℕ) : constantCoeff (Φ.coeff l) = 0 := by
    rw [← eval_zero, ← Polynomial.coeff_map, map_eval_eval₂_sum_C_mul_X_pow]
    simp [constantCoeff_eq, hG.coeff_eq_zero (d := 0) (by simpa using hd.ne)]
  have hcard : Nat.card (Fin (d * r + r + 1)) < Nat.card (σ × Fin (r + 1)) := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin, Fintype.card_prod] at hσ ⊢
    nlinarith
  obtain ⟨y, hy0, hy⟩ := exists_ne_zero_forall_eval_eq_zero
    (fun l : Fin (d * r + r + 1) ↦ Φ.coeff l) (fun l ↦ hΦ l) hcard
  refine ⟨fun i ↦ ∑ j : Fin (r + 1), Polynomial.C (y (i, j)) * Polynomial.X ^ (j : ℕ),
    fun h ↦ hy0 ?_, ?_⟩
  · ext ⟨i, j⟩
    simpa [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Fin.val_inj] using
      congrArg (Polynomial.coeff · j) (congrFun h i)
  · ext l
    rw [Polynomial.coeff_zero]
    rcases lt_or_ge l (d * r + r + 1) with hl | hl
    · rw [← map_eval_eval₂_sum_C_mul_X_pow, Polynomial.coeff_map]
      exact hy ⟨l, hl⟩
    · exact Polynomial.coeff_eq_zero_of_natDegree_lt
        ((natDegree_eval_le_of_isHomogeneous hG hr (hx y)).trans_lt hl)

end MvPolynomial

/-- **Tsen's theorem for `k(t)`.** The rational function field over an algebraically closed
field is quasi-algebraically closed.
(blueprint: `lemma-cohomology-multiplicative-group--7`) -/
instance RatFunc.isQuasiAlgClosed (k : Type*) [Field k] [IsAlgClosed k] :
    IsQuasiAlgClosed (RatFunc k) where
  exists_ne_zero_and_eval_eq_zero {N d} F hF hd hN := by
    obtain ⟨c, hc, G, hG⟩ := exists_map_eq_C_mul (nonZeroDivisors (Polynomial k)) F
    have hinj := IsFractionRing.injective (Polynomial k) (RatFunc k)
    have hGh : G.IsHomogeneous d := fun s hs ↦ hF fun h0 ↦ hs (hinj (by
      rw [← coeff_map, hG, coeff_C_mul, h0, mul_zero, map_zero]))
    obtain ⟨x, hx, hGx⟩ := exists_ne_zero_eval_eq_zero_of_isHomogeneous_polynomial G hGh hd
      (by simpa using hN)
    refine ⟨algebraMap _ _ ∘ x, fun h ↦ hx (funext fun i ↦ hinj
      ((congrFun h i).trans (map_zero _).symm)), ?_⟩
    have := congrArg (MvPolynomial.eval (algebraMap (Polynomial k) (RatFunc k) ∘ x)) hG
    rw [MvPolynomial.eval_map, ← eval₂_comp, hGx, map_zero, map_mul, MvPolynomial.eval_C, eq_comm,
      mul_eq_zero] at this
    exact this.resolve_left ((map_ne_zero_iff _ hinj).mpr (nonZeroDivisors.ne_zero hc))

/-- **Tsen's theorem.** A field `K` of transcendence degree at most one over an algebraically
closed field `k` is quasi-algebraically closed. This covers the function field of a curve over
`k` and all its algebraic extensions.
(blueprint: `lemma-cohomology-multiplicative-group--7`) -/
@[stacks 03RD]
theorem IsQuasiAlgClosed.of_trdeg_le_one {K : Type*} [Field K] (k : Type*) [Field k]
    [IsAlgClosed k] [Algebra k K] (h : Algebra.trdeg k K ≤ 1) : IsQuasiAlgClosed K := by
  -- Proof sketch: if `trdeg = 0` then `K` is algebraic over `k`, hence equal to `k`. Otherwise
  -- `K` is algebraic over a subfield `k(t) ≅ RatFunc k`, and `IsQuasiAlgClosed.of_isAlgebraic`
  -- applies.
  by_cases halg : Algebra.IsAlgebraic k K
  · exact IsCField.of_ringEquiv
      (RingEquiv.ofBijective (algebraMap k K) IsAlgClosed.algebraMap_bijective_of_isIntegral)
  rw [← Algebra.transcendental_iff_not_isAlgebraic] at halg
  obtain ⟨t, ht⟩ := Algebra.Transcendental.transcendental (R := k) (A := K)
  have hb : IsTranscendenceBasis k fun _ : PUnit ↦ t :=
    (algebraicIndependent_unique_type_iff.mpr ht).isTranscendenceBasis_of_trdeg_le_of_finite
      (by simpa using h)
  have := hb.isAlgebraic_field
  rw [Set.range_const] at this
  have : IsQuasiAlgClosed (IntermediateField.adjoin k {t}) :=
    IsCField.of_ringEquiv (RatFunc.algEquivOfTranscendental t ht).toRingEquiv
  exact IsQuasiAlgClosed.of_isAlgebraic (IntermediateField.adjoin k {t}) K
