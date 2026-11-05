import Langlands.Global.PrimitiveAdelicGauss
import Langlands.Global.PrimitiveAdelicBasis

/-! # Height reduction for the actual adelic `GL(2)` -/

noncomputable section

universe u

open scoped NNReal Topology Matrix

namespace Langlands.Global.PrimitiveAdelicHeight

open NumberField

variable (F : Type u) [Field F] [NumberField F]

/-! ## Heights under locally bounded matrices -/

/-- An adelic matrix whose entries are integral at a finite place does not increase
the local maximum norm there. -/
theorem finiteNorm_mulVec_le {n : ℕ} (k : Matrix (Fin n) (Fin n) (Adeles F))
    (x : Vector F n) (v : FinitePlace F) (hk : ∀ i j, ‖finiteProjection F v (k i j)‖ ≤ 1) :
    finiteNorm F n (k *ᵥ x) v ≤ finiteNorm F n x v := by
  unfold finiteNorm
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => ?_
  change ‖finiteProjection F v (∑ j, k i j * x j)‖ ≤ _
  rw [map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun j _ => ?_
  rw [map_mul, norm_mul]
  calc ‖finiteProjection F v (k i j)‖ * ‖finiteProjection F v (x j)‖
      ≤ 1 * ‖fun i : Fin n => finiteProjection F v (x i)‖ :=
        mul_le_mul (hk i j) (norm_le_pi_norm (fun i : Fin n => finiteProjection F v (x i)) j)
          (norm_nonneg _) zero_le_one
    _ = ‖fun i : Fin n => finiteProjection F v (x i)‖ := one_mul _

/-- An adelic matrix whose entries are bounded by `A` at an infinite place
increases the local maximum norm there by at most the factor `n A`. -/
theorem infiniteNorm_mulVec_le {n : ℕ} (k : Matrix (Fin n) (Fin n) (Adeles F))
    (x : Vector F n) (w : InfinitePlace F) {A : ℝ} (hA : 0 ≤ A)
    (hk : ∀ i j, ‖infiniteProjection F w (k i j)‖ ≤ A) :
    infiniteNorm F n (k *ᵥ x) w ≤ (n * A) * infiniteNorm F n x w := by
  unfold infiniteNorm
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hA)
    (norm_nonneg _))).mpr fun i => ?_
  change ‖infiniteProjection F w (∑ j, k i j * x j)‖ ≤ _
  rw [map_sum]
  calc ‖∑ j, infiniteProjection F w (k i j * x j)‖
      ≤ ∑ j, ‖infiniteProjection F w (k i j * x j)‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin n, A * ‖fun i : Fin n => infiniteProjection F w (x i)‖ := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [map_mul, norm_mul]
        exact mul_le_mul (hk i j)
          (norm_le_pi_norm (fun i : Fin n => infiniteProjection F w (x i)) j)
          (norm_nonneg _) hA
    _ = (n * A) * ‖fun i : Fin n => infiniteProjection F w (x i)‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]

/-- Local comparisons of primitive vectors give the corresponding comparison of
heights, with the archimedean multiplicities. -/
theorem height_le_of_local_le {n : ℕ} {x y : Vector F n} (hx : IsPrimitive F n x)
    (hy : IsPrimitive F n y) {M : ℝ} (hM : 0 ≤ M)
    (hfin : ∀ v, finiteNorm F n x v ≤ finiteNorm F n y v)
    (hinf : ∀ w, infiniteNorm F n x w ≤ M * infiniteNorm F n y w) :
    height F n x ≤ M ^ Module.finrank ℚ F * height F n y := by
  have hprod : ∏ w : InfinitePlace F, infiniteNorm F n x w ^ w.mult ≤
      M ^ Module.finrank ℚ F * ∏ w : InfinitePlace F, infiniteNorm F n y w ^ w.mult := by
    calc ∏ w : InfinitePlace F, infiniteNorm F n x w ^ w.mult
        ≤ ∏ w : InfinitePlace F, (M * infiniteNorm F n y w) ^ w.mult :=
          Finset.prod_le_prod₀ (fun w _ => pow_nonneg (norm_nonneg _) _)
            (fun w _ => pow_le_pow_left₀ (norm_nonneg _) (hinf w) _)
      _ = M ^ Module.finrank ℚ F * ∏ w : InfinitePlace F, infiniteNorm F n y w ^ w.mult := by
          rw [← InfinitePlace.sum_mult_eq, ← Finset.prod_pow_eq_pow_sum,
            ← Finset.prod_mul_distrib]
          simp only [mul_pow]
  have hfp : ∏ᶠ v, finiteNorm F n x v ≤ ∏ᶠ v, finiteNorm F n y v :=
    finprod_le_finprod₀ (hx.hasFiniteMulSupport F n) (fun v => norm_nonneg _)
      (hy.hasFiniteMulSupport F n) hfin
  unfold height
  calc (∏ w : InfinitePlace F, infiniteNorm F n x w ^ w.mult) * ∏ᶠ v, finiteNorm F n x v
      ≤ (M ^ Module.finrank ℚ F * ∏ w : InfinitePlace F, infiniteNorm F n y w ^ w.mult) *
          ∏ᶠ v, finiteNorm F n y v :=
        mul_le_mul hprod hfp (finprod_nonneg fun v => norm_nonneg _)
          (mul_nonneg (pow_nonneg hM _)
            (Finset.prod_nonneg fun w _ => pow_nonneg (norm_nonneg _) _))
    _ = M ^ Module.finrank ℚ F * ((∏ w : InfinitePlace F, infiniteNorm F n y w ^ w.mult) *
          ∏ᶠ v, finiteNorm F n y v) := mul_assoc _ _ _

/-- An actual invertible adelic matrix with integral finite entries and infinite
entries bounded by `A` changes heights of primitive vectors by at most
`(n A) ^ [F : ℚ]`. -/
theorem height_mulVec_le {n : ℕ} (k : AdelicGL F n) {A : ℝ} (hA : 0 ≤ A)
    (hfin : ∀ v i j, ‖finiteProjection F v (k i j)‖ ≤ 1)
    (hinf : ∀ w i j, ‖infiniteProjection F w (k i j)‖ ≤ A)
    {x : Vector F n} (hx : IsPrimitive F n x) :
    height F n (k.val *ᵥ x) ≤ (n * A) ^ Module.finrank ℚ F * height F n x :=
  height_le_of_local_le F (hx.mulVec F n k) hx (mul_nonneg (Nat.cast_nonneg n) hA)
    (fun v => finiteNorm_mulVec_le F k.val x v (hfin v))
    (fun w => infiniteNorm_mulVec_le F k.val x w hA (hinf w))

/-! ## A bounded completion of a normalized first column -/

/-- The actual adele whose local component is `1` where the first coordinate of `y`
has local norm one and `0` elsewhere. -/
def indicatorAdele (y : Vector F 2) : Adeles F :=
  (fun w => if ‖infiniteProjection F w (y 0)‖ = 1 then 1 else 0,
    ⟨fun v => if ‖finiteProjection F v (y 0)‖ = 1 then 1 else 0,
      Filter.Eventually.of_forall fun v => by
        dsimp only
        split_ifs
        · exact one_mem _
        · exact zero_mem _⟩)

@[simp] theorem finiteProjection_indicatorAdele (y : Vector F 2) (v : FinitePlace F) :
    finiteProjection F v (indicatorAdele F y) =
      if ‖finiteProjection F v (y 0)‖ = 1 then 1 else 0 := rfl

@[simp] theorem infiniteProjection_indicatorAdele (y : Vector F 2) (w : InfinitePlace F) :
    infiniteProjection F w (indicatorAdele F y) =
      if ‖infiniteProjection F w (y 0)‖ = 1 then 1 else 0 := rfl

/-- The matrix with first column `y` and second column a standard basis vector
chosen place by place through the indicator adele. -/
def completionMatrix (y : Vector F 2) : Matrix (Fin 2) (Fin 2) (Adeles F) :=
  !![y 0, 1 - indicatorAdele F y; y 1, indicatorAdele F y]

theorem norm_ite_le_one {K : Type*} [NormedField K] (p : Prop) [Decidable p] :
    ‖(if p then 1 else 0 : K)‖ ≤ 1 := by
  split_ifs <;> simp

theorem norm_one_sub_ite_le_one {K : Type*} [NormedField K] (p : Prop) [Decidable p] :
    ‖(1 - if p then 1 else 0 : K)‖ ≤ 1 := by
  split_ifs <;> simp

/-- The local determinant of the completion of a vector of maximum norm one has
norm one. -/
theorem norm_local_completion_det {K : Type*} [NormedField K] (z : Fin 2 → K)
    (hz : ‖z‖ = 1) :
    ‖z 0 * (if ‖z 0‖ = 1 then 1 else 0) - (1 - if ‖z 0‖ = 1 then 1 else 0) * z 1‖ = 1 := by
  have h0 : ‖z 0‖ ≤ 1 := hz ▸ norm_le_pi_norm z 0
  have h1 : ‖z 1‖ ≤ 1 := hz ▸ norm_le_pi_norm z 1
  split_ifs with h
  · simpa using h
  · have h1' : ‖z 1‖ = 1 := by
      by_contra hne
      have hlt : ‖z‖ < 1 := (pi_norm_lt_iff one_pos).mpr
        (Fin.forall_fin_two.mpr ⟨lt_of_le_of_ne h0 h, lt_of_le_of_ne h1 hne⟩)
      linarith
    simpa using h1'

theorem completionMatrix_det (y : Vector F 2) :
    (completionMatrix F y).det =
      y 0 * indicatorAdele F y - (1 - indicatorAdele F y) * y 1 := by
  rw [completionMatrix, Matrix.det_fin_two_of]

theorem norm_finiteProjection_completionMatrix_det (y : Vector F 2) (v : FinitePlace F)
    (hy : finiteNorm F 2 y v = 1) :
    ‖finiteProjection F v (completionMatrix F y).det‖ = 1 := by
  rw [completionMatrix_det, map_sub, map_mul, map_mul, map_sub, map_one,
    finiteProjection_indicatorAdele]
  exact norm_local_completion_det (fun i => finiteProjection F v (y i)) hy

theorem norm_infiniteProjection_completionMatrix_det (y : Vector F 2) (w : InfinitePlace F)
    (hy : infiniteNorm F 2 y w = 1) :
    ‖infiniteProjection F w (completionMatrix F y).det‖ = 1 := by
  rw [completionMatrix_det, map_sub, map_mul, map_mul, map_sub, map_one,
    infiniteProjection_indicatorAdele]
  exact norm_local_completion_det (fun i => infiniteProjection F w (y i)) hy

/-- An adele with all finite local norms one and nonzero infinite components is a unit. -/
theorem isUnit_of_local_norm (a : Adeles F)
    (hfin : ∀ v, ‖finiteProjection F v a‖ = 1) (hinf : ∀ w, infiniteProjection F w a ≠ 0) :
    IsUnit a := by
  have h1 : IsUnit a.1 := Pi.isUnit_iff.mpr fun w => isUnit_iff_ne_zero.mpr (hinf w)
  have h2 : IsUnit a.2 := by
    refine RestrictedProduct.isUnit_of_eventually_isUnit (fun v => ?_)
      (Filter.Eventually.of_forall fun v => ?_)
    · apply isUnit_iff_ne_zero.mpr
      apply norm_ne_zero_iff.mp
      change ‖finiteProjection F v a‖ ≠ 0
      rw [hfin v]
      exact one_ne_zero
    · have hn : ‖a.2 v‖ = 1 := hfin v
      have hne : a.2 v ≠ 0 := norm_ne_zero_iff.mp (by rw [hn]; exact one_ne_zero)
      have hmem : a.2 v ∈ v.adicCompletionIntegers F := by
        simpa only [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
          ← Valued.toNormedField.norm_le_one_iff] using hn.le
      have hinvmem : (a.2 v)⁻¹ ∈ v.adicCompletionIntegers F := by
        have : ‖(a.2 v)⁻¹‖ ≤ 1 := by rw [norm_inv, hn, inv_one]
        simpa only [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
          ← Valued.toNormedField.norm_le_one_iff] using this
      exact ⟨hmem, ⟨⟨⟨_, hmem⟩, ⟨_, hinvmem⟩, Subtype.ext (mul_inv_cancel₀ hne),
        Subtype.ext (inv_mul_cancel₀ hne)⟩, rfl⟩⟩
  exact Prod.isUnit_iff.mpr ⟨h1, h2⟩

theorem isUnit_completionMatrix (y : Vector F 2) (hfin : ∀ v, finiteNorm F 2 y v = 1)
    (hinf : ∀ w, infiniteNorm F 2 y w = 1) : IsUnit (completionMatrix F y) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  refine isUnit_of_local_norm F _
    (fun v => norm_finiteProjection_completionMatrix_det F y v (hfin v)) fun w => ?_
  apply norm_ne_zero_iff.mp
  rw [norm_infiniteProjection_completionMatrix_det F y w (hinf w)]
  exact one_ne_zero

/-! ## The bounded-times-triangular decomposition -/

/-- The first column of an actual adelic matrix, a primitive vector. -/
def firstColumn (g : AdelicGL F 2) : Vector F 2 :=
  g.val *ᵥ rational F 2 ![1, 0]

theorem firstColumn_isPrimitive (g : AdelicGL F 2) : IsPrimitive F 2 (firstColumn F g) :=
  ⟨g, ![1, 0], by simp, rfl⟩

/-- The actual content idele of the first column. -/
def firstContent (g : AdelicGL F 2) : Ideles F :=
  contentIdele F 2 (firstColumn F g) (firstColumn_isPrimitive F g)

/-- The first column divided by its content idele; all its local maximum norms are one. -/
def firstDirection (g : AdelicGL F 2) : Vector F 2 :=
  normalizedVector F 2 (firstColumn F g) (firstColumn_isPrimitive F g)

/-- The bounded factor: the completion of the normalized first column. -/
def boundedFactor (g : AdelicGL F 2) : AdelicGL F 2 :=
  (isUnit_completionMatrix F (firstDirection F g)
    (finiteNorm_normalizedVector F 2 _ _) (infiniteNorm_normalizedVector F 2 _ _)).unit

/-- The upper triangular factor `k⁻¹ g` of the decomposition `g = k (k⁻¹ g)`. -/
def triangularFactor (g : AdelicGL F 2) : AdelicGL F 2 :=
  (boundedFactor F g)⁻¹ * g

theorem boundedFactor_val (g : AdelicGL F 2) :
    (boundedFactor F g).val = completionMatrix F (firstDirection F g) := rfl

theorem boundedFactor_mul_triangularFactor (g : AdelicGL F 2) :
    boundedFactor F g * triangularFactor F g = g :=
  mul_inv_cancel_left _ _

theorem mulVec_rational_first_apply (M : Matrix (Fin 2) (Fin 2) (Adeles F)) (i : Fin 2) :
    (M *ᵥ rational F 2 ![1, 0]) i = M i 0 := by
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, rational]

theorem boundedFactor_mulVec_first (g : AdelicGL F 2) :
    (boundedFactor F g).val *ᵥ rational F 2 ![1, 0] = firstDirection F g := by
  funext i
  rw [mulVec_rational_first_apply, boundedFactor_val]
  fin_cases i <;> rfl

theorem triangularFactor_mulVec_first (g : AdelicGL F 2) :
    (triangularFactor F g).val *ᵥ rational F 2 ![1, 0] =
      (firstContent F g).val • rational F 2 ![1, 0] := by
  have hc : g.val *ᵥ rational F 2 ![1, 0] = (firstContent F g).val • firstDirection F g :=
    (contentIdele_smul_normalizedVector F 2 _ _).symm
  rw [triangularFactor, Units.val_mul, ← Matrix.mulVec_mulVec, hc, Matrix.mulVec_smul,
    ← boundedFactor_mulVec_first F g, Matrix.mulVec_mulVec, ← Units.val_mul,
    inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem triangularFactor_zero_zero (g : AdelicGL F 2) :
    triangularFactor F g 0 0 = (firstContent F g).val := by
  have h := congrFun (triangularFactor_mulVec_first F g) 0
  rw [mulVec_rational_first_apply] at h
  simpa [rational] using h

theorem triangularFactor_one_zero (g : AdelicGL F 2) :
    triangularFactor F g 1 0 = 0 := by
  have h := congrFun (triangularFactor_mulVec_first F g) 1
  rw [mulVec_rational_first_apply] at h
  simpa [rational] using h

/-- The second diagonal idele of the triangular factor. -/
def secondDiagonal (g : AdelicGL F 2) : Ideles F :=
  Matrix.GeneralLinearGroup.det (triangularFactor F g) * (firstContent F g)⁻¹

theorem firstContent_mul_secondDiagonal (g : AdelicGL F 2) :
    firstContent F g * secondDiagonal F g =
      Matrix.GeneralLinearGroup.det (triangularFactor F g) := by
  rw [secondDiagonal, mul_comm, inv_mul_cancel_right]

theorem triangularFactor_one_one (g : AdelicGL F 2) :
    triangularFactor F g 1 1 = (secondDiagonal F g).val := by
  have h := congrArg Units.val (firstContent_mul_secondDiagonal F g)
  rw [Units.val_mul, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two,
    triangularFactor_zero_zero, triangularFactor_one_zero, mul_zero, sub_zero] at h
  exact ((firstContent F g).isUnit.mul_left_cancel h).symm

theorem finiteProjection_boundedFactor_le (g : AdelicGL F 2) (v : FinitePlace F)
    (i j : Fin 2) : ‖finiteProjection F v (boundedFactor F g i j)‖ ≤ 1 := by
  have hy : ‖fun i : Fin 2 => finiteProjection F v (firstDirection F g i)‖ = 1 :=
    finiteNorm_normalizedVector F 2 _ _ v
  have hyi (i : Fin 2) : ‖finiteProjection F v (firstDirection F g i)‖ ≤ 1 :=
    hy ▸ norm_le_pi_norm (fun i : Fin 2 => finiteProjection F v (firstDirection F g i)) i
  change ‖finiteProjection F v (completionMatrix F (firstDirection F g) i j)‖ ≤ 1
  fin_cases i <;> fin_cases j
  · exact hyi 0
  · change ‖finiteProjection F v (1 - indicatorAdele F (firstDirection F g))‖ ≤ 1
    rw [map_sub, map_one, finiteProjection_indicatorAdele]
    exact norm_one_sub_ite_le_one _
  · exact hyi 1
  · change ‖finiteProjection F v (indicatorAdele F (firstDirection F g))‖ ≤ 1
    rw [finiteProjection_indicatorAdele]
    exact norm_ite_le_one _

theorem infiniteProjection_boundedFactor_le (g : AdelicGL F 2) (w : InfinitePlace F)
    (i j : Fin 2) : ‖infiniteProjection F w (boundedFactor F g i j)‖ ≤ 1 := by
  have hy : ‖fun i : Fin 2 => infiniteProjection F w (firstDirection F g i)‖ = 1 :=
    infiniteNorm_normalizedVector F 2 _ _ w
  have hyi (i : Fin 2) : ‖infiniteProjection F w (firstDirection F g i)‖ ≤ 1 :=
    hy ▸ norm_le_pi_norm (fun i : Fin 2 => infiniteProjection F w (firstDirection F g i)) i
  change ‖infiniteProjection F w (completionMatrix F (firstDirection F g) i j)‖ ≤ 1
  fin_cases i <;> fin_cases j
  · exact hyi 0
  · change ‖infiniteProjection F w (1 - indicatorAdele F (firstDirection F g))‖ ≤ 1
    rw [map_sub, map_one, infiniteProjection_indicatorAdele]
    exact norm_one_sub_ite_le_one _
  · exact hyi 1
  · change ‖infiniteProjection F w (indicatorAdele F (firstDirection F g))‖ ≤ 1
    rw [infiniteProjection_indicatorAdele]
    exact norm_ite_le_one _

theorem finiteProjection_det_boundedFactor (g : AdelicGL F 2) (v : FinitePlace F) :
    ‖finiteProjection F v (Matrix.GeneralLinearGroup.det (boundedFactor F g)).val‖ = 1 :=
  norm_finiteProjection_completionMatrix_det F _ v (finiteNorm_normalizedVector F 2 _ _ v)

theorem infiniteProjection_det_boundedFactor (g : AdelicGL F 2) (w : InfinitePlace F) :
    ‖infiniteProjection F w (Matrix.GeneralLinearGroup.det (boundedFactor F g)).val‖ = 1 :=
  norm_infiniteProjection_completionMatrix_det F _ w (infiniteNorm_normalizedVector F 2 _ _ w)

theorem full_det_boundedFactor (g : AdelicGL F 2) :
    IdeleAbsoluteValue.full F (Matrix.GeneralLinearGroup.det (boundedFactor F g)) = 1 := by
  apply Units.ext
  apply NNReal.eq
  rw [IdeleAbsoluteValue.coe_full]
  have hinf (w : InfinitePlace F) :
      ‖(Matrix.GeneralLinearGroup.det (boundedFactor F g)).val.1 w‖ = 1 :=
    infiniteProjection_det_boundedFactor F g w
  have hfin (v : FinitePlace F) :
      ‖(Matrix.GeneralLinearGroup.det (boundedFactor F g)).val.2 v‖ = 1 :=
    finiteProjection_det_boundedFactor F g v
  simp only [hinf, hfin, one_pow, Finset.prod_const_one, finprod_one, mul_one]
  rfl

/-- The normalized absolute value of the determinant is the product of those of
the two diagonal ideles of the triangular factor. -/
theorem full_det_eq (g : AdelicGL F 2) :
    IdeleAbsoluteValue.full F (Matrix.GeneralLinearGroup.det g) =
      IdeleAbsoluteValue.full F (firstContent F g) *
        IdeleAbsoluteValue.full F (secondDiagonal F g) := by
  have h := congrArg Matrix.GeneralLinearGroup.det (boundedFactor_mul_triangularFactor F g)
  rw [map_mul] at h
  rw [← h, map_mul, full_det_boundedFactor, one_mul, ← map_mul,
    firstContent_mul_secondDiagonal]

/-- The height of the first column is the normalized absolute value of its content. -/
theorem rationalHeight_first (g : AdelicGL F 2) :
    rationalHeight F 2 g ![1, 0] =
      ((IdeleAbsoluteValue.full F (firstContent F g) : ℝ≥0) : ℝ) := by
  rw [firstContent, full_contentIdele, positiveHeight_val]
  rfl

/-- The bounded factor changes heights of primitive vectors by at most `2 ^ [F : ℚ]`. -/
theorem height_boundedFactor_mulVec_le (g : AdelicGL F 2) {x : Vector F 2}
    (hx : IsPrimitive F 2 x) :
    height F 2 ((boundedFactor F g).val *ᵥ x) ≤ 2 ^ Module.finrank ℚ F * height F 2 x := by
  have h := height_mulVec_le F (boundedFactor F g) zero_le_one
    (finiteProjection_boundedFactor_le F g) (infiniteProjection_boundedFactor_le F g) hx
  norm_num at h
  exact h

/-- The triangular factor applied to a rational vector, rescaled to the rank-two
vector of the Gauss bound. -/
theorem triangularFactor_mulVec_rational (g : AdelicGL F 2) (l m : F) :
    (triangularFactor F g).val *ᵥ rational F 2 ![l, m] =
      (secondDiagonal F g).val • rankTwoVector F (firstContent F g * (secondDiagonal F g)⁻¹)
        (triangularFactor F g 0 1 * ((secondDiagonal F g)⁻¹).val) l m := by
  have h00 := triangularFactor_zero_zero F g
  have h10 := triangularFactor_one_zero F g
  have h11 := triangularFactor_one_one F g
  have hinv : (secondDiagonal F g).val * ((secondDiagonal F g)⁻¹).val = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  funext i
  fin_cases i
  · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, rational, rankTwoVector,
      Pi.smul_apply, smul_eq_mul, Units.val_mul]
    simp only [Fin.zero_eta, Matrix.cons_val_zero, Matrix.cons_val_one, h00]
    linear_combination (-(diagonal F l * (firstContent F g).val +
      triangularFactor F g 0 1 * diagonal F m)) * hinv
  · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, rational, rankTwoVector,
      Pi.smul_apply, smul_eq_mul]
    simp [h10, h11]

/-! ## The Hermite bound and the reduction inequality -/

/-- **Hermite bound for the actual adelic `GL(2)`.** There is a constant `C` such that
every actual adelic matrix maps some nonzero rational vector to a vector of height at
most `C` times the square root of the normalized absolute value of its determinant. -/
theorem exists_rationalHeight_le_sqrt_det :
    ∃ C : ℝ, 0 < C ∧ ∀ g : AdelicGL F 2, ∃ r : Fin 2 → F, r ≠ 0 ∧
      rationalHeight F 2 g r ≤
        C * Real.sqrt ((IdeleAbsoluteValue.full F (Matrix.GeneralLinearGroup.det g) : ℝ≥0) : ℝ) := by
  obtain ⟨C₀, hC₀, hgauss⟩ := exists_rankTwoVector_height_le F
  refine ⟨2 ^ Module.finrank ℚ F * C₀, mul_pos (pow_pos two_pos _) hC₀, fun g => ?_⟩
  set t₁ := firstContent F g
  set t₂ := secondDiagonal F g
  obtain ⟨l, m, hlm, hH⟩ := hgauss (t₁ * t₂⁻¹) (triangularFactor F g 0 1 * (t₂⁻¹).val)
  have hr : (![l, m] : Fin 2 → F) ≠ 0 := by
    intro h
    rcases hlm with hl | hm
    · exact hl (by simpa using congrFun h 0)
    · exact hm (by simpa using congrFun h 1)
  refine ⟨![l, m], hr, ?_⟩
  set w := rankTwoVector F (t₁ * t₂⁻¹) (triangularFactor F g 0 1 * (t₂⁻¹).val) l m
  have hb : (triangularFactor F g).val *ᵥ rational F 2 ![l, m] = t₂.val • w :=
    triangularFactor_mulVec_rational F g l m
  have hbp : IsPrimitive F 2 ((triangularFactor F g).val *ᵥ rational F 2 ![l, m]) :=
    ⟨triangularFactor F g, ![l, m], hr, rfl⟩
  have hw : IsPrimitive F 2 w := by
    have h := hbp.smul F 2 t₂⁻¹
    rwa [hb, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul] at h
  have hg : rationalHeight F 2 g ![l, m] =
      height F 2 ((boundedFactor F g).val *ᵥ
        ((triangularFactor F g).val *ᵥ rational F 2 ![l, m])) := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, boundedFactor_mul_triangularFactor]
    rfl
  set a : ℝ := ((IdeleAbsoluteValue.full F t₁ : ℝ≥0) : ℝ)
  set b : ℝ := ((IdeleAbsoluteValue.full F t₂ : ℝ≥0) : ℝ)
  have ha : 0 < a := IdeleAbsoluteValue.full_pos F t₁
  have hb0 : 0 < b := IdeleAbsoluteValue.full_pos F t₂
  have hx : ((IdeleAbsoluteValue.full F (t₁ * t₂⁻¹) : ℝ≥0) : ℝ) = a * b⁻¹ := by
    simp only [map_mul, map_inv, Units.val_mul, NNReal.coe_mul, Units.val_inv_eq_inv_val,
      NNReal.coe_inv, a, b]
  have hdet : ((IdeleAbsoluteValue.full F (Matrix.GeneralLinearGroup.det g) : ℝ≥0) : ℝ) =
      a * b := by
    rw [full_det_eq]
    simp only [Units.val_mul, NNReal.coe_mul, a, b, t₁, t₂]
  have hsqrt : Real.sqrt (a * b) = b * Real.sqrt (a * b⁻¹) := by
    have : a * b = a * b⁻¹ * (b * b) := by field_simp
    rw [this, Real.sqrt_mul (mul_nonneg ha.le (inv_nonneg.mpr hb0.le)),
      Real.sqrt_mul_self hb0.le, mul_comm]
  rw [hg, hdet]
  calc height F 2 ((boundedFactor F g).val *ᵥ
        ((triangularFactor F g).val *ᵥ rational F 2 ![l, m]))
      ≤ 2 ^ Module.finrank ℚ F * height F 2
          ((triangularFactor F g).val *ᵥ rational F 2 ![l, m]) :=
        height_boundedFactor_mulVec_le F g hbp
    _ = 2 ^ Module.finrank ℚ F * (b * height F 2 w) := by
        rw [hb, hw.height_smul F 2]
    _ ≤ 2 ^ Module.finrank ℚ F * (b * (C₀ * Real.sqrt (a * b⁻¹))) := by
        rw [← hx]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hH hb0.le)
          (pow_nonneg zero_le_two _)
    _ = 2 ^ Module.finrank ℚ F * C₀ * Real.sqrt (a * b) := by
        rw [hsqrt]
        ring

/-- **Reduction theory for the actual adelic `GL(2)`.** There is a constant `c` such
that every actual adelic matrix, after right multiplication by a rational matrix,
is the product of an actual adelic matrix with integral finite entries, infinite
entries of norm at most one and determinant of local norm one everywhere, and an
actual upper triangular adelic matrix whose diagonal ideles satisfy
`|t₁| ≤ c |t₂|`. -/
theorem exists_reduction :
    ∃ c : ℝ, 0 < c ∧ ∀ g : AdelicGL F 2, ∃ (γ : RationalGL F 2) (k b : AdelicGL F 2)
      (t₁ t₂ : Ideles F),
      g * AdelicGL.rational F 2 γ = k * b ∧
      (∀ v i j, ‖finiteProjection F v (k i j)‖ ≤ 1) ∧
      (∀ w i j, ‖infiniteProjection F w (k i j)‖ ≤ 1) ∧
      (∀ v, ‖finiteProjection F v (Matrix.GeneralLinearGroup.det k).val‖ = 1) ∧
      (∀ w, ‖infiniteProjection F w (Matrix.GeneralLinearGroup.det k).val‖ = 1) ∧
      b 0 0 = t₁.val ∧ b 1 0 = 0 ∧ b 1 1 = t₂.val ∧
      ((IdeleAbsoluteValue.full F t₁ : ℝ≥0) : ℝ) ≤
        c * ((IdeleAbsoluteValue.full F t₂ : ℝ≥0) : ℝ) := by
  obtain ⟨C, hC, hherm⟩ := exists_rationalHeight_le_sqrt_det F
  refine ⟨C ^ 2, pow_pos hC 2, fun g => ?_⟩
  have hn : 0 < 2 := two_pos
  set h := minimumAdaptedMatrix F 2 g hn
  refine ⟨minimumBasisChange F 2 g hn, boundedFactor F h, triangularFactor F h,
    firstContent F h, secondDiagonal F h, (boundedFactor_mul_triangularFactor F h).symm,
    finiteProjection_boundedFactor_le F h, infiniteProjection_boundedFactor_le F h,
    finiteProjection_det_boundedFactor F h, infiniteProjection_det_boundedFactor F h,
    triangularFactor_zero_zero F h, triangularFactor_one_zero F h,
    triangularFactor_one_one F h, ?_⟩
  obtain ⟨r, hr, hle⟩ := hherm h
  have hfirst : firstVector F 2 hn = ![1, 0] := by
    funext i
    fin_cases i <;> simp [firstVector]
  have hmin := minimumAdaptedMatrix_first_min F 2 g hn r hr
  rw [hfirst, rationalHeight_first] at hmin
  rw [full_det_eq] at hle
  set a : ℝ := ((IdeleAbsoluteValue.full F (firstContent F h) : ℝ≥0) : ℝ)
  set b : ℝ := ((IdeleAbsoluteValue.full F (secondDiagonal F h) : ℝ≥0) : ℝ)
  have ha : 0 < a := IdeleAbsoluteValue.full_pos F _
  have hb : 0 < b := IdeleAbsoluteValue.full_pos F _
  have hab : a ≤ C * Real.sqrt (a * b) := by
    have := hmin.trans hle
    simpa only [Units.val_mul, NNReal.coe_mul, a, b] using this
  have hsq : a ^ 2 ≤ C ^ 2 * (a * b) := by
    have h2 := pow_le_pow_left₀ ha.le hab 2
    rwa [mul_pow, Real.sq_sqrt (mul_nonneg ha.le hb.le)] at h2
  nlinarith

end Langlands.Global.PrimitiveAdelicHeight
