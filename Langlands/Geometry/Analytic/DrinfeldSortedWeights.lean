import Langlands.Geometry.Analytic.DrinfeldLatticeBasis
import Mathlib.Order.Interval.Finset.Fin

/-! # Comparing sorted weights in normalized bases -/

noncomputable section

universe v w u

namespace Langlands.Analytic.VectorNorm

open Set
open scoped ENNReal

section WeightedNorm

variable {F : Type v} [NormedField F] [IsUltrametricDist F]
  {V : Type w} [AddCommGroup V] [Module F V]
  {ι : Type u} [Fintype ι] [Nonempty ι]

/-- The maximum of the absolute values of the coordinates multiplied by the given
positive weights. -/
def ofBasisWeights (b : Module.Basis ι F V) (w : ι → ℝ) (hw : ∀ i, 0 < w i) :
    VectorNorm F V where
  toFun a := Finset.univ.sup' Finset.univ_nonempty fun i => ‖b.repr a i‖ * w i
  pos' a ha := by
    obtain ⟨i, hi⟩ : ∃ i, b.repr a i ≠ 0 := by
      by_contra! h
      exact ha (b.repr.injective (by
        rw [_root_.map_zero]
        ext i
        exact h i))
    exact (mul_pos (norm_pos_iff.2 hi) (hw i)).trans_le
      (Finset.le_sup' (fun j => ‖b.repr a j‖ * w j) (Finset.mem_univ i))
  smul' t a := by
    simp only [LinearEquiv.map_smul, Finsupp.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
    exact (Finset.mul₀_sup' (norm_nonneg t) _ _ _).symm
  add_le_max' a a' := by
    apply (Finset.sup'_le_iff _ _).2
    intro i _
    simp only [map_add, Finsupp.add_apply]
    calc ‖b.repr a i + b.repr a' i‖ * w i
        ≤ max (‖b.repr a i‖) (‖b.repr a' i‖) * w i :=
          mul_le_mul_of_nonneg_right (IsUltrametricDist.norm_add_le_max _ _) (hw i).le
      _ = max (‖b.repr a i‖ * w i) (‖b.repr a' i‖ * w i) :=
          max_mul_of_nonneg _ _ (hw i).le
      _ ≤ _ := max_le_max (Finset.le_sup' (fun j => ‖b.repr a j‖ * w j) (Finset.mem_univ i))
        (Finset.le_sup' (fun j => ‖b.repr a' j‖ * w j) (Finset.mem_univ i))

@[simp]
theorem ofBasisWeights_apply_basis (b : Module.Basis ι F V) (w : ι → ℝ)
    (hw : ∀ i, 0 < w i) (i : ι) : ofBasisWeights b w hw (b i) = w i := by
  classical
  change (Finset.univ.sup' Finset.univ_nonempty fun j => ‖b.repr (b i) j‖ * w j) = _
  apply le_antisymm
  · refine (Finset.sup'_le_iff _ _).2 fun j _ => ?_
    by_cases h : i = j
    · subst j
      simp
    · simp [Module.Basis.repr_self, h, (hw i).le]
  · simpa only [Module.Basis.repr_self, Finsupp.single_eq_same, norm_one, one_mul] using
      (Finset.le_sup' (fun j => ‖b.repr (b i) j‖ * w j) (Finset.mem_univ i))

theorem isAdaptedBasis_ofBasisWeights (b : Module.Basis ι F V) (w : ι → ℝ)
    (hw : ∀ i, 0 < w i) : (ofBasisWeights b w hw).IsAdaptedBasis b := by
  intro c i
  rw [map_smul, ofBasisWeights_apply_basis]
  change ‖c i‖ * w i ≤ Finset.univ.sup' Finset.univ_nonempty
    (fun j => ‖b.repr (∑ k, c k • b k) j‖ * w j)
  rw [← b.equivFun_symm_apply, ← b.equivFun_apply, b.equivFun.apply_symm_apply]
  exact Finset.le_sup' (fun j => ‖c j‖ * w j) (Finset.mem_univ i)

end WeightedNorm

section Comparison

variable {F : Type v} [NormedField F] {V : Type w} [AddCommGroup V] [Module F V]
  {ν η μ : VectorNorm F V} {d : ℕ} {b c : Module.Basis (Fin (d + 1)) F V}

private theorem finrank_span_basis_image (s : Set (Fin (d + 1))) [Fintype s]
    (b : Module.Basis (Fin (d + 1)) F V) :
    Module.finrank F (Submodule.span F (b '' s)) = Fintype.card s := by
  rw [image_eq_range]
  exact finrank_span_eq_card (b.linearIndependent.comp _ Subtype.val_injective)

/-- A pointwise comparison of two norms implies the same comparison of their sorted
weights in two adapted bases normalized for the same reference norm. -/
theorem sorted_weights_le_mul (hb : ν.IsAdaptedBasis b) (hc : η.IsAdaptedBasis c)
    (hμb : μ.IsNormalizedBasis b) (hμc : μ.IsNormalizedBasis c)
    (hν : Monotone fun i => ν (b i)) (hη : Monotone fun i => η (c i))
    {C : ℝ} (hC : 0 ≤ C) (hle : ∀ a, ν a ≤ C * η a) (i : Fin (d + 1)) :
    ν (b i) ≤ C * η (c i) := by
  classical
  let : FiniteDimensional F V := c.finiteDimensional_of_finite
  let S := Submodule.span F (c '' Iic i)
  let T := Submodule.span F (b '' Ici i)
  have hS : Module.finrank F S = i.val + 1 := by
    change Module.finrank F (Submodule.span F (c '' Iic i)) = _
    rw [finrank_span_basis_image, Fintype.card_Iic, Fin.card_Iic]
  have hT : Module.finrank F T = d + 1 - i.val := by
    change Module.finrank F (Submodule.span F (b '' Ici i)) = _
    rw [finrank_span_basis_image, Fintype.card_Ici, Fin.card_Ici]
  have hsup := Submodule.finrank_mono (show S ⊔ T ≤ ⊤ from le_top)
  rw [finrank_top, Module.finrank_eq_card_basis c, Fintype.card_fin] at hsup
  have hsum := S.finrank_sup_add_finrank_inf_eq T
  rw [hS, hT] at hsum
  obtain ⟨x, hx⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := F) (M := ↥(S ⊓ T))).1
    (by have := i.isLt; omega)
  let a : V := x
  have ha : a ≠ 0 := fun h => hx (Subtype.ext h)
  have hprefix : η a ≤ η (c i) * μ a := by
    apply (hc.apply_le_iff (mul_nonneg (η.nonneg _) (μ.nonneg _)) _).2
    intro j
    by_cases hj : j ≤ i
    · have hr := (hμc.1.apply_le_iff (μ.nonneg a) a).1 le_rfl j
      rw [hμc.2, mul_one] at hr
      calc ‖c.repr a j‖ * η (c j) ≤ ‖c.repr a j‖ * η (c i) :=
            mul_le_mul_of_nonneg_left (hη hj) (norm_nonneg _)
        _ ≤ μ a * η (c i) := mul_le_mul_of_nonneg_right hr (η.nonneg _)
        _ = η (c i) * μ a := mul_comm _ _
    · have hz : c.repr a j = 0 := Finsupp.notMem_support_iff.1 fun h =>
        hj (c.repr_support_subset_of_mem_span (Iic i) x.2.1 h)
      rw [hz, norm_zero, zero_mul]
      exact mul_nonneg (η.nonneg _) (μ.nonneg _)
  have hsuffix : ν (b i) * μ a ≤ ν a := by
    obtain ⟨j, -, hj⟩ := Finset.exists_max_image Finset.univ (fun j => ‖b.repr a j‖)
      Finset.univ_nonempty
    have hμa : μ a ≤ ‖b.repr a j‖ :=
      (hμb.1.apply_le_iff (norm_nonneg _) a).2 fun k => by
        rw [hμb.2, mul_one]
        exact hj k (Finset.mem_univ k)
    have hj' : i ≤ j := by
      by_contra h
      have hz : b.repr a j = 0 := Finsupp.notMem_support_iff.1 fun hm =>
        h (b.repr_support_subset_of_mem_span (Ici i) x.2.2 hm)
      rw [hz, norm_zero] at hμa
      exact (μ.pos ha).not_ge hμa
    calc ν (b i) * μ a ≤ ‖b.repr a j‖ * ν (b j) := by
          rw [mul_comm (ν (b i))]
          exact mul_le_mul hμa (hν hj') (ν.nonneg _) (norm_nonneg _)
      _ ≤ ν a := (hb.apply_le_iff (ν.nonneg a) a).1 le_rfl j
  apply le_of_mul_le_mul_right _ (μ.pos ha)
  calc ν (b i) * μ a ≤ ν a := hsuffix
    _ ≤ C * η a := hle a
    _ ≤ C * (η (c i) * μ a) := mul_le_mul_of_nonneg_left hprefix hC
    _ = C * η (c i) * μ a := by ring

private theorem exp_log_weight_diff (a a' b b' : ℝ)
    (ha : 0 < a) (ha' : 0 < a') (hb : 0 < b) (hb' : 0 < b') :
    Real.exp ((Real.log a - Real.log b) - (Real.log a' - Real.log b')) = a / b * (b' / a') := by
  rw [show (Real.log a - Real.log b) - (Real.log a' - Real.log b') =
      (Real.log a - Real.log b) + (Real.log b' - Real.log a') by ring,
    Real.exp_add, Real.exp_sub, Real.exp_sub, Real.exp_log ha, Real.exp_log hb,
    Real.exp_log hb', Real.exp_log ha']

/-- In one adapted basis, log-distance less than `ε` is exactly the strict spread test
on the differences of the log weights. -/
theorem IsAdaptedBasis.distRatio_lt_exp_iff (hb : ν.IsAdaptedBasis b) (hc : η.IsAdaptedBasis b)
    (ε : ℝ) : distRatio ν η < ENNReal.ofReal (Real.exp ε) ↔ ∀ i j,
      (Real.log (ν (b i)) - Real.log (η (b i))) -
        (Real.log (ν (b j)) - Real.log (η (b j))) < ε := by
  rw [hb.distRatio_lt_iff hc (Real.exp_pos ε)]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  rw [← exp_log_weight_diff _ _ _ _
    (ν.pos (b.ne_zero i)) (ν.pos (b.ne_zero j)) (η.pos (b.ne_zero i)) (η.pos (b.ne_zero j)),
    Real.exp_lt_exp]

/-- Comparing the sorted log weights of two norms in their own adapted bases, each
normalized for the same reference norm, cannot increase their log-distance. -/
theorem log_weight_diff_lt_of_distRatio_lt (hb : ν.IsAdaptedBasis b) (hc : η.IsAdaptedBasis c)
    (hμb : μ.IsNormalizedBasis b) (hμc : μ.IsNormalizedBasis c)
    (hν : Monotone fun i => ν (b i)) (hη : Monotone fun i => η (c i))
    {ε : ℝ} (hd : distRatio ν η < ENNReal.ofReal (Real.exp ε)) (i j : Fin (d + 1)) :
    (Real.log (ν (b i)) - Real.log (η (c i))) -
      (Real.log (ν (b j)) - Real.log (η (c j))) < ε := by
  have : Nontrivial V := ⟨⟨b 0, 0, b.ne_zero 0⟩⟩
  obtain ⟨hA, hB⟩ := ratioSup_ne_top_of_distRatio_lt hd
  let A := (ratioSup ν η).toReal
  let B := (ratioSup η ν).toReal
  have hratio (ν η : VectorNorm F V) (h : ratioSup ν η ≠ ⊤) (a : V) :
      ν a ≤ (ratioSup ν η).toReal * η a := by
    by_cases ha : a = 0
    · simp [ha]
    exact (div_le_iff₀ (η.pos ha)).1 ((ENNReal.ofReal_le_iff_le_toReal h).1 (le_ratioSup ν η a))
  have hAi := sorted_weights_le_mul hb hc hμb hμc hν hη ENNReal.toReal_nonneg (hratio ν η hA) i
  have hBj := sorted_weights_le_mul hc hb hμc hμb hη hν ENNReal.toReal_nonneg (hratio η ν hB) j
  rw [← Real.exp_lt_exp, exp_log_weight_diff _ _ _ _
    (ν.pos (b.ne_zero i)) (ν.pos (b.ne_zero j)) (η.pos (c.ne_zero i)) (η.pos (c.ne_zero j))]
  refine (mul_le_mul ((div_le_iff₀ (η.pos (c.ne_zero i))).2 hAi)
    ((div_le_iff₀ (ν.pos (b.ne_zero j))).2 hBj)
    (div_nonneg (η.nonneg _) (ν.nonneg _)) (show 0 ≤ A from ENNReal.toReal_nonneg)).trans_lt ?_
  change A * B < Real.exp ε
  rw [show A * B = (distRatio ν η).toReal from ENNReal.toReal_mul.symm]
  exact ENNReal.toReal_lt_of_lt_ofReal hd

end Comparison

end Langlands.Analytic.VectorNorm
