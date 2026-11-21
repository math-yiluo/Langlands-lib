import Langlands.GroupScheme.Quaternionic.QuaternionicPureDiagonalIsotropy
import Langlands.LinearAlgebra.NumberFieldQuadraticRepresentation
import Mathlib.LinearAlgebra.QuadraticForm.Radical
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Representation by the rank-six quadratic norm form -/

noncomputable section

universe u

open NumberField QuadraticMap
open scoped TensorProduct

namespace Langlands.GroupScheme.Quaternionic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000

/-- The weights of the sum of three quadratic norms for the root square `c`. -/
def rankThreeNormWeights {R : Type*} [Ring R] (a : Fin 3 → R) (c : R) : Fin 3 ⊕ Fin 3 → R :=
  Sum.elim a (fun i => -c * a i)

@[simp]
theorem rankThreeNormWeights_inl {R : Type*} [Ring R] (a : Fin 3 → R) (c : R) (i : Fin 3) :
    rankThreeNormWeights a c (.inl i) = a i := rfl

@[simp]
theorem rankThreeNormWeights_inr {R : Type*} [Ring R] (a : Fin 3 → R) (c : R) (i : Fin 3) :
    rankThreeNormWeights a c (.inr i) = -c * a i := rfl

private theorem map_rankThreeNormWeights {R S : Type*} [Ring R] [Ring S]
    (g : R →+* S) (a : Fin 3 → R) (c : R) :
    g ∘ rankThreeNormWeights a c = rankThreeNormWeights (g ∘ a) (g c) := by
  funext i
  cases i <;> simp only [Function.comp_apply, rankThreeNormWeights_inl, rankThreeNormWeights_inr,
    map_mul, map_neg]

private theorem delta_neg_of_positive_weights {a : Fin 3 → ℝ} {c d : ℝ}
    (ha : ∀ i, 0 < a i) (hc : c < 0) (hd : d ≠ 0) (h : HasNonzeroSkewNormZero a c d) : d < 0 := by
  by_contra hn
  have hp : 0 < d := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hd)
  obtain ⟨u₀, u₁, v₀, v₁, ⟨i, hi⟩, heq⟩ := h
  let N : ℝ → ℝ → ℝ := fun x y => x ^ 2 - c * y ^ 2
  have hN (x y : ℝ) : 0 ≤ N x y :=
    sub_nonneg.mpr ((mul_nonpos_of_nonpos_of_nonneg hc.le (sq_nonneg y)).trans (sq_nonneg x))
  have hNp (x y : ℝ) (hxy : x ≠ 0 ∨ y ≠ 0) : 0 < N x y := by
    apply sub_pos.mpr
    rcases hxy with hx | hy
    · exact (mul_nonpos_of_nonpos_of_nonneg hc.le (sq_nonneg y)).trans_lt (sq_pos_of_ne_zero hx)
    · exact (mul_neg_of_neg_of_pos hc (sq_pos_of_ne_zero hy)).trans_le (sq_nonneg x)
  let s := fun i => a i * (N (u₀ i) (u₁ i) + d * N (v₀ i) (v₁ i))
  have hs (i : Fin 3) : 0 ≤ s i := mul_nonneg (ha i).le
    (add_nonneg (hN _ _) (mul_nonneg hp.le (hN _ _)))
  have hsi : s i = 0 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hs j)).mp heq i (Finset.mem_univ i)
  have hsi' : 0 < s i := by
    apply mul_pos (ha i)
    rcases hi with h₀ | h₁ | h₂ | h₃
    · exact add_pos_of_pos_of_nonneg (hNp _ _ (Or.inl h₀)) (mul_nonneg hp.le (hN _ _))
    · exact add_pos_of_pos_of_nonneg (hNp _ _ (Or.inr h₁)) (mul_nonneg hp.le (hN _ _))
    · exact add_pos_of_nonneg_of_pos (hN _ _) (mul_pos hp (hNp _ _ (Or.inl h₂)))
    · exact add_pos_of_nonneg_of_pos (hN _ _) (mul_pos hp (hNp _ _ (Or.inr h₃)))
  exact hsi'.ne' hsi

private theorem exists_value_on_axis {K J : Type*} [Field K] [Fintype J] [DecidableEq J]
    (w : J → K) (i : J) {t x : K} (hw : w i ≠ 0) (hx : x ^ 2 = t / w i) :
    ∃ z : J → K, weightedSumSquares K w z = t := by
  refine ⟨Pi.single i x, ?_⟩
  rw [weightedSumSquares_apply, Finset.sum_eq_single i, Pi.single_eq_same, smul_eq_mul, ← _root_.sq,
    hx, mul_comm (w i), div_mul_cancel₀ _ hw]
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, mul_zero, smul_zero]
  · simp

private theorem represents_rankThreeNorm_real (a : Fin 3 → ℝ) (c d : ℝ)
    (ha : ∀ i, a i ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) (hl : HasNonzeroSkewNormZero a c d) :
    ∃ x : (Fin 3 ⊕ Fin 3) → ℝ,
      weightedSumSquares ℝ (rankThreeNormWeights a c) x = -(∏ i, a i) * d := by
  let w := rankThreeNormWeights a c
  let t := -(∏ i, a i) * d
  have hwn (i : Fin 3 ⊕ Fin 3) : w i ≠ 0 := by
    rcases i with i | i
    · exact ha i
    · exact mul_ne_zero (neg_ne_zero.mpr hc) (ha i)
  have haxis (i : Fin 3 ⊕ Fin 3) (h : 0 ≤ t / w i) :
      ∃ x : (Fin 3 ⊕ Fin 3) → ℝ, weightedSumSquares ℝ w x = t :=
    exists_value_on_axis w i (hwn i) (Real.sq_sqrt h)
  by_cases hp : ∀ i, 0 < w i
  · have ha' (i : Fin 3) : 0 < a i := hp (.inl i)
    have hc' : c < 0 := neg_pos.mp ((mul_pos_iff_of_pos_right (ha' 0)).mp (hp (.inr 0)))
    have hd' := delta_neg_of_positive_weights ha' hc' hd hl
    have ht : 0 < t := by
      dsimp [t]
      rw [Fin.prod_univ_three]
      exact mul_pos_of_neg_of_neg (neg_neg_of_pos (mul_pos (mul_pos (ha' 0) (ha' 1)) (ha' 2))) hd'
    exact haxis (.inl 0) (div_nonneg ht.le (hp (.inl 0)).le)
  by_cases hn : ∀ i, w i < 0
  · have ha' (i : Fin 3) : a i < 0 := hn (.inl i)
    have hc' : c < 0 := by
      by_contra hc0
      have hnonneg := mul_nonneg_of_nonpos_of_nonpos (neg_nonpos.mpr (le_of_not_gt hc0)) (ha' 0).le
      exact (not_lt_of_ge hnonneg) (hn (.inr 0))
    have hl' : HasNonzeroSkewNormZero (-a) c d := by
      obtain ⟨u₀, u₁, v₀, v₁, hne, h⟩ := hl
      exact ⟨u₀, u₁, v₀, v₁, hne, by
        simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, h, neg_zero]⟩
    have hd' := delta_neg_of_positive_weights (fun i => neg_pos.mpr (ha' i)) hc' hd hl'
    have ht : t < 0 := by
      dsimp [t]
      rw [Fin.prod_univ_three]
      exact mul_neg_of_pos_of_neg (neg_pos.mpr
        (mul_neg_of_pos_of_neg (mul_pos_of_neg_of_neg (ha' 0) (ha' 1)) (ha' 2))) hd'
    exact haxis (.inl 0) (div_nonneg_of_nonpos ht.le (hn (.inl 0)).le)
  push Not at hp hn
  obtain ⟨i, hi⟩ := hp
  obtain ⟨j, hj⟩ := hn
  rcases le_total 0 t with ht | ht
  · exact haxis j (div_nonneg ht hj)
  · exact haxis i (div_nonneg_of_nonpos ht hi)

private theorem map_weightedSumSquares {K L J : Type*} [Field K] [Field L] [Fintype J]
    (g : K →+* L) (w x : J → K) :
    g (weightedSumSquares K w x) = weightedSumSquares L (g ∘ w) (g ∘ x) := by
  simp only [weightedSumSquares_apply, smul_eq_mul, map_sum, map_mul, Function.comp_apply]

/-- The rank-six norm form represents negative the product of the Hermitian
  weights times `d`, under the real skew-isotropy conditions. -/
def NumberFieldRankThreeHermitianNormValueStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (a : Fin 3 → F) (c d : F),
    (∀ i, a i ≠ 0) → c ≠ 0 → d ≠ 0 →
    (∀ v : InfinitePlace F, v.IsReal →
      HasNonzeroSkewNormZero (algebraMap F v.Completion ∘ a)
        (algebraMap F v.Completion c) (algebraMap F v.Completion d)) →
    ∃ x : (Fin 3 ⊕ Fin 3) → F,
      weightedSumSquares F (rankThreeNormWeights a c) x = -(∏ i, a i) * d

/-- At a real place a definite norm form gets the sign of the target from skew
  isotropy. A complex place admits a square-root solution on a coordinate axis. -/
theorem numberFieldRankThreeHermitianNormValue : NumberFieldRankThreeHermitianNormValueStatement.{u} := by
  intro F _ _ a c d ha hc hd hl
  let : Invertible (2 : F) := invertibleOfNonzero (two_ne_zero : (2 : F) ≠ 0)
  let w := rankThreeNormWeights a c
  let q := weightedSumSquares F w
  let t := -(∏ i, a i) * d
  have hwn (i : Fin 3 ⊕ Fin 3) : w i ≠ 0 := by
    rcases i with i | i
    · exact ha i
    · exact mul_ne_zero (neg_ne_zero.mpr hc) (ha i)
  have hq : q.polarBilin.Nondegenerate := by
    change (weightedSumSquares F w).polarBilin.Nondegenerate
    rw [nondegenerate_polar_iff, nondegenerate_iff_radical_eq_bot, QuadraticForm.radical_weightedSumSquares]
    apply (Submodule.eq_bot_iff _).mpr
    intro x hx
    funext i
    exact Pi.mem_spanSubset_iff.mp hx i (hwn i)
  have hdim : 4 ≤ Module.finrank F ((Fin 3 ⊕ Fin 3) → F) := by
    norm_num [Module.finrank_pi, Fintype.card_sum]
  apply numberFieldQuadraticRepresentation_of_archimedean q hq hdim t
  intro v
  let K := v.Completion
  let f := algebraMap F K
  let e := QuadraticIsotropy.weightedSumSquaresScalarExtension K (QuadraticMap.IsometryEquiv.refl q)
  suffices h : ∃ y : (Fin 3 ⊕ Fin 3) → K, weightedSumSquares K (f ∘ w) y = f t by
    obtain ⟨y, hy⟩ := h
    exact ⟨e.symm y, (e.symm.map_app y).trans hy⟩
  by_cases hv : v.IsReal
  · let g := (InfinitePlace.Completion.ringEquivRealOfIsReal hv).toRingHom
    let j := g.comp f
    have hiso : HasNonzeroSkewNormZero (j ∘ a) (j c) (j d) := (hl v hv).map g g.injective
    obtain ⟨y, hy⟩ := represents_rankThreeNorm_real (j ∘ a) (j c) (j d)
      (fun i => (map_ne_zero_iff j j.injective).mpr (ha i))
      ((map_ne_zero_iff j j.injective).mpr hc) ((map_ne_zero_iff j j.injective).mpr hd) hiso
    let y' := (InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm ∘ y
    refine ⟨y', g.injective ?_⟩
    rw [map_weightedSumSquares]
    have hcomp : g ∘ y' = y := funext fun i => (InfinitePlace.Completion.ringEquivRealOfIsReal hv).apply_symm_apply _
    rw [hcomp, show g ∘ (f ∘ w) = j ∘ w from rfl, map_rankThreeNormWeights, hy]
    change -(∏ i, j (a i)) * j d = j t
    simp [t]
  · let g := InfinitePlace.Completion.ringEquivComplexOfIsComplex
      (InfinitePlace.not_isReal_iff_isComplex.mp hv)
    let i : Fin 3 ⊕ Fin 3 := .inl 0
    obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq (g (f t / f (w i))) (by decide : 0 < (2 : ℕ))
    have hpow : (g.symm b) ^ 2 = f t / f (w i) := g.injective (by rw [map_pow, g.apply_symm_apply, hb])
    exact exists_value_on_axis (f ∘ w) i ((map_ne_zero_iff f f.injective).mpr (hwn i)) hpow

end Langlands.GroupScheme.Quaternionic
