import Langlands.Global.RankinSelberg.ComplexSquareZetaConvergence

/-! # Polynomial weights in the matrix variable of the equal-rank unfolding -/

noncomputable section

open Function MeasureTheory
open Langlands.GeneralLinear
open scoped Matrix.Norms.Operator NNReal SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquet

open ArchimedeanLocal
open ComplexGodement (normPower)
open Langlands.Archimedean.ComplexGeneralLinearHaarDensity
open Langlands.RankinSelberg.GLDeterminantDensity

variable {n : ℕ}

local notation "G" => Langlands.GeneralLinear n ℂ
local notation "Mat" => Matrix (Fin n) (Fin n) ℂ

local instance : MeasurableSpace G := borel _
local instance : BorelSpace G := ⟨rfl⟩

private def sizePolynomial (X : Mat) : ℝ :=
  1 + ∑ i, ∑ j, ‖X i j‖ ^ 2

private theorem sizePolynomial_one_le (X : Mat) : 1 ≤ sizePolynomial X :=
  le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)

private theorem hasTemperateGrowth_sizePolynomial : HasTemperateGrowth (sizePolynomial (n := n)) := by
  let entryLinear (i j : Fin n) : Mat →ₗ[ℝ] ℂ :=
    { toFun := fun X => X i j
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact (HasTemperateGrowth.const 1).add (HasTemperateGrowth.sum fun i _ =>
    HasTemperateGrowth.sum fun j _ => (hasTemperateGrowth_norm_sq (H := ℂ)).comp
      (entryLinear i j).toContinuousLinearMap.hasTemperateGrowth)

private theorem max_one_norm_le_sizePolynomial (X : Mat) :
    max 1 ‖X‖ ≤ ((n : ℝ) + 1) * sizePolynomial X := by
  have hX := sizePolynomial_one_le X
  have hNg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hP0 := zero_le_one.trans hX
  have hEntry (i j : Fin n) : ‖X i j‖ ≤ sizePolynomial X := by
    have h := Finset.single_le_sum
      (f := fun i : Fin n => ∑ j, ‖X i j‖ ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
    have h' := Finset.single_le_sum (f := fun j => ‖X i j‖ ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
    unfold sizePolynomial
    nlinarith [sq_nonneg (‖X i j‖ - 1), h'.trans h]
  refine max_le ?_ ?_
  · exact (one_mul (1 : ℝ)).symm.trans_le (mul_le_mul (by linarith) hX zero_le_one (by positivity))
  · rw [Matrix.linfty_opNorm_def]
    let B : NNReal := ⟨((n : ℝ) + 1) * sizePolynomial X, by positivity⟩
    change (↑(Finset.univ.sup fun i => ∑ j : Fin n, ‖X i j‖₊) : ℝ) ≤ (B : ℝ)
    suffices Finset.univ.sup (fun i => ∑ j : Fin n, ‖X i j‖₊) ≤ B from this
    refine Finset.sup_le fun i _ => ?_
    change ((∑ j : Fin n, ‖X i j‖₊ : NNReal) : ℝ) ≤ (B : ℝ)
    push_cast
    calc
      _ ≤ ∑ _ : Fin n, sizePolynomial X := Finset.sum_le_sum fun j _ => hEntry i j
      _ = (n : ℝ) * sizePolynomial X := by simp [nsmul_eq_mul]
      _ ≤ ((n : ℝ) + 1) * sizePolynomial X :=
        mul_le_mul_of_nonneg_right (by linarith) hP0

/-- An arbitrary polynomial power of the matrix norm can be included in the
Schwartz factor without raising the threshold for the determinant exponent. -/
def ComplexLocalSquarePositiveWeightStatement : Prop :=
  ∀ (μ : Measure G) [μ.IsHaarMeasure] (Φ : 𝓢(Mat, ℂ)) (j : ℕ) (p : ℝ), (n : ℝ) ≤ p →
    Integrable (fun g : G =>
      max 1 ‖g.val‖ ^ j * ‖Φ g.val‖ * complexNormalizedAbs g.val.det ^ p) μ

theorem complexLocalSquarePositiveWeight : ComplexLocalSquarePositiveWeightStatement (n := n) := by
  intro μ _ Φ j p hp
  let w (X : Mat) := (((n : ℝ) + 1) * sizePolynomial X) ^ j
  have hw : HasTemperateGrowth w :=
    ((HasTemperateGrowth.const _).mul hasTemperateGrowth_sizePolynomial).pow j
  let Ψ := SchwartzMap.smulLeftCLM ℂ w Φ
  have hΨ (X : Mat) : ‖Ψ X‖ = w X * ‖Φ X‖ := by
    change ‖SchwartzMap.smulLeftCLM ℂ w Φ X‖ = _
    have h0 : 0 ≤ w X := pow_nonneg (mul_nonneg (by positivity)
      (zero_le_one.trans (sizePolynomial_one_le X))) _
    rw [SchwartzMap.smulLeftCLM_apply_apply hw, norm_smul, Real.norm_of_nonneg h0]
  have hpow (g : G) : ‖normPower (p : ℂ) (determinant g)‖ =
      complexNormalizedAbs g.val.det ^ p := by
    have hdet : 0 < complexNormalizedAbs g.val.det := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr g.det_ne_zero)
    exact Complex.norm_cpow_eq_rpow_re_of_pos hdet p
  have hm : Integrable (fun g : G => Ψ g.val * normPower (p : ℂ) (determinant g)) μ := by
    simpa only [pow_zero, Complex.ofReal_one, one_mul] using
      ComplexSquareZeta.integrable_height_detNormPower μ 0 Ψ (p : ℂ) (by simpa using hp)
  have hc : Continuous (fun g : G => complexNormalizedAbs g.val.det ^ p) := by
    simpa only [hpow] using (ComplexSquareZeta.continuous_detNormPower (n := n) (p : ℂ)).norm
  refine hm.norm.mono'
    ((((continuous_const.max Units.continuous_val.norm).pow j).mul
      (Φ.continuous.comp Units.continuous_val).norm).mul hc).aestronglyMeasurable
    (ae_of_all _ fun g => ?_)
  change ‖max 1 ‖g.val‖ ^ j * ‖Φ g.val‖ * complexNormalizedAbs g.val.det ^ p‖ ≤
    ‖Ψ g.val * normPower (p : ℂ) (determinant g)‖
  have hDet : 0 ≤ complexNormalizedAbs g.val.det ^ p := Real.rpow_nonneg (sq_nonneg _) _
  rw [Real.norm_of_nonneg (mul_nonneg (by positivity) hDet), norm_mul, hpow, hΨ]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (zero_le_one.trans (le_max_left _ _)) (max_one_norm_le_sizePolynomial _) j)
      (norm_nonneg _)) hDet

private theorem detNormSq_temperate :
    HasTemperateGrowth (fun X : Mat => ‖X.det‖ ^ 2) := by
  classical
  have hdet : HasTemperateGrowth (fun X : Mat => X.det) := by
    simp only [Matrix.det_apply']
    apply HasTemperateGrowth.sum
    intro e _
    apply (HasTemperateGrowth.const _).mul
    have h (s : Finset (Fin n)) : HasTemperateGrowth (fun X : Mat => ∏ i ∈ s, X (e i) i) := by
      induction s using Finset.induction_on with
      | empty => simpa only [Finset.prod_empty] using (HasTemperateGrowth.const (1 : ℂ))
      | insert i s hi ih =>
        simp only [Finset.prod_insert hi]
        let L : Mat →ₗ[ℝ] ℂ := ⟨⟨fun X => X (e i) i, fun _ _ => rfl⟩, fun _ _ => rfl⟩
        exact L.toContinuousLinearMap.hasTemperateGrowth.mul ih
    exact h Finset.univ
  exact (hasTemperateGrowth_norm_sq (H := ℂ)).comp hdet

/-- A matrix weight on the region of absolute convergence is bounded in the
Schwartz topology. The dominating function of the test vanishes at zero. -/
theorem exists_squarePositiveWeight_bound (μ : Measure G) [μ.IsHaarMeasure]
    (j : ℕ) (p : ℝ) (hp : (n : ℝ) ≤ p) :
    ∃ q : 𝓢(Mat, ℂ) → ℝ, Continuous q ∧ q 0 = 0 ∧ ∀ Φ,
      (∫ g : G, max 1 ‖g.val‖ ^ j * ‖Φ g.val‖ * complexNormalizedAbs g.val.det ^ p ∂μ) ≤ q Φ := by
  let : SecondCountableTopology G := Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology
  let ν := complexGeneralLinearHaar n
  let c := Measure.haarScalarFactor μ ν
  have hμ : μ = c • ν := Measure.isMulLeftInvariant_eq_smul _ _
  obtain ⟨l, hl⟩ := exists_nat_ge (p - (n : ℝ))
  let δ (X : Mat) := ‖X.det‖ ^ 2
  let W (X : Mat) := (((n : ℝ) + 1) * sizePolynomial X) ^ j * (1 + δ X) ^ l
  have hW : HasTemperateGrowth W :=
    (((HasTemperateGrowth.const _).mul hasTemperateGrowth_sizePolynomial).pow j).mul
      (((HasTemperateGrowth.const _).add detNormSq_temperate).pow l)
  let T := SchwartzMap.smulLeftCLM ℂ W
  let q (Φ : 𝓢(Mat, ℂ)) := (c : ℝ) * ‖(T Φ).toLp 1 (matrixLebesgue n)‖
  have hzero : (0 : 𝓢(Mat, ℂ)).toLp 1 (matrixLebesgue n) = 0 :=
    (SchwartzMap.toLpCLM ℝ ℂ 1 (matrixLebesgue n)).map_zero
  refine ⟨q, (SchwartzMap.continuous_toLp.comp T.continuous).norm.const_mul _, by simp [q, hzero], ?_⟩
  intro Φ
  let F (X : Mat) := max 1 ‖X‖ ^ j * ‖Φ X‖ * δ X ^ p
  have hI : Integrable (fun g : G => F g.val) ν :=
    complexLocalSquarePositiveWeight ν Φ j p hp
  let U : Set Mat := Set.range (Units.val : G → Mat)
  let μ₀ := matrixLebesgue n
  have hU : MeasurableSet U := Units.isOpenEmbedding_val.isOpen_range.measurableSet
  have hFI := (integrable_weightedRestriction_iff n normSqHom continuous_normSqHom μ₀ F).mp hI
  have hGI : Integrable (fun X => ‖T Φ X‖) μ₀ := (T Φ).integrable.norm
  have hle : (∫ X in U, matrixWeight n normSqHom X • F X ∂μ₀) ≤
      ∫ X, ‖T Φ X‖ ∂μ₀ := by
    refine (integral_mono_ae hFI hGI.restrict ?_).trans
      (integral_mono_measure Measure.restrict_le_self (.of_forall fun _ => norm_nonneg _) hGI)
    filter_upwards [ae_restrict_mem hU] with X hX
    obtain ⟨g, rfl⟩ := hX
    let X := g.val
    have hδ : 0 < δ X :=
      sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (Matrix.GeneralLinearGroup.det_ne_zero g))
    have hWeight : (matrixWeight n normSqHom X : ℝ) = δ X ^ (-(n : ℝ)) := by
      rw [matrixWeight, NNReal.coe_pow, NNReal.coe_inv, inv_pow, Real.rpow_neg hδ.le,
        Real.rpow_natCast]
      rfl
    have hpow : δ X ^ (p - (n : ℝ)) ≤ (1 + δ X) ^ l := by
      calc
        _ ≤ (1 + δ X) ^ (p - (n : ℝ)) :=
          Real.rpow_le_rpow hδ.le (by linarith) (sub_nonneg.mpr hp)
        _ ≤ _ := by
          rw [← Real.rpow_natCast]
          exact Real.rpow_le_rpow_of_exponent_le (by linarith) hl
    have hP := pow_le_pow_left₀ (show 0 ≤ max 1 ‖X‖ by positivity)
      (max_one_norm_le_sizePolynomial X) j
    have hW0 : 0 ≤ W X := mul_nonneg
      (pow_nonneg (mul_nonneg (by positivity) (zero_le_one.trans (sizePolynomial_one_le X))) _)
      (pow_nonneg (by linarith) _)
    change (matrixWeight n normSqHom X : ℝ) * F X ≤ ‖SchwartzMap.smulLeftCLM ℂ W Φ X‖
    rw [hWeight, SchwartzMap.smulLeftCLM_apply_apply hW, norm_smul, Real.norm_of_nonneg hW0]
    calc
      _ = (max 1 ‖X‖ ^ j * δ X ^ (p - (n : ℝ))) * ‖Φ X‖ := by
        dsimp only [F]
        rw [Real.rpow_sub hδ, Real.rpow_neg hδ.le]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul hP hpow (Real.rpow_nonneg hδ.le _) (by
        exact pow_nonneg (mul_nonneg (by positivity) (zero_le_one.trans (sizePolynomial_one_le X))) _))
        (norm_nonneg _)
  change (∫ g : G, F g.val ∂μ) ≤ q Φ
  rw [hμ, integral_smul_nnreal_measure, NNReal.smul_def]
  change (c : ℝ) * (∫ g : G, F g.val ∂weightedRestriction n normSqHom μ₀) ≤
    (c : ℝ) * ‖(T Φ).toLp 1 μ₀‖
  rw [integral_weightedRestriction n normSqHom continuous_normSqHom μ₀ F]
  rw [SchwartzMap.norm_toLp_one]
  exact mul_le_mul_of_nonneg_left hle c.coe_nonneg

end Langlands.Global.RankinSelbergGlobal.ComplexJacquet
