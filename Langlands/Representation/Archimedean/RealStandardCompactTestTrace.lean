import Langlands.Representation.Archimedean.RealStandardCompactProjection

/-! # Compact trace comparison for continuous tests -/

noncomputable section

open MeasureTheory Langlands.LocalFactor.Archimedean
open scoped Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.RealStandardCompactAverage

attribute [local instance 100] LieRing.ofAssociativeRing

open GramFormula OrthogonalFinitePolynomial PrincipalSeriesExtension
  RealInducedBlockBound RealInducedStandardBound

local notation "G" => Langlands.GeneralLinear
local notation "K" => fun n => Matrix.unitaryGroup (Fin n) ℝ
local notation "V" => fun n ds => kFiniteFunctions (realStandardModule n ds)
  (unitaryCompact ℝ n)

variable {n : ℕ}

private theorem continuous_signedOrthogonalPart :
    Continuous (signedOrthogonalPart : G n ℝ → K n) := by
  refine Continuous.subtype_mk ?_ _
  apply continuous_matrix
  intro i j
  have h (l : ℕ) : Continuous fun x : G n ℝ =>
      (Real.sqrt (gram l (x : Matrix (Fin n) (Fin n) ℝ)))⁻¹ :=
    (Real.continuous_sqrt.comp ((contDiff_gram l).continuous.comp Units.continuous_val)).inv₀
      (fun x => (Real.sqrt_pos.2 (gram_pos x l)).ne')
  exact (((contDiff_gramColumn i j).continuous.comp Units.continuous_val).mul (h i)).mul
    (h ((i : ℕ) + 1))

private def compactWeight (ds : List RealBlock) (g : G n ℝ) : C(K n, ℂ) where
  toFun y := extension (shiftedExponent n (realPositionExponent ds)) 1 (Unitary.toUnits y * g)
  continuous_toFun := ((contMDiff_extension (shiftedExponent n (realPositionExponent ds))
    (P := 1) (φ := 1) (by intro k; simp)).continuous).comp
      (continuous_unitary_toUnits.mul continuous_const)

/-- Extend the test column from the compact group using the signed orthogonal part. -/
def continuousColumn (φ : C(K n, ℂ)) (y : K n) : C(G n ℝ, ℂ) where
  toFun x := φ ((signedOrthogonalPart x)⁻¹ * y)
  continuous_toFun := φ.continuous.comp
    (continuous_signedOrthogonalPart.inv.mul continuous_const)

@[simp]
theorem continuousColumn_apply (φ : C(K n, ℂ)) (y : K n) (x : G n ℝ) :
    continuousColumn φ y x = φ ((signedOrthogonalPart x)⁻¹ * y) := rfl

private theorem continuous_sign_family (ds : List RealBlock) (I : List (Fin n))
    (F : K n → C(G n ℝ, ℂ)) (hF : Continuous (fun z : K n × G n ℝ => F z.1 z.2)) :
    Continuous fun z : K n × G n ℝ => signFilters ds I (F z.1) z.2 := by
  induction I with
  | nil => exact hF
  | cons i I ih =>
    simp only [signFilters_cons, signFilter_apply]
    exact continuous_const.mul (ih.add (continuous_const.mul
      (ih.comp (continuous_fst.prodMk (continuous_const.mul continuous_snd)))))

private theorem continuous_coefficient_family (p : ℕ) (j : ℤ)
    (F : K n → C(G n ℝ, ℂ)) (hF : Continuous (fun z : K n × G n ℝ => F z.1 z.2)) :
    Continuous fun z : K n × G n ℝ => blockFourierCoefficient n p j (F z.1) z.2 := by
  unfold blockFourierCoefficient
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' ?_ _ _
  have harg : Continuous fun z : (K n × G n ℝ) × ℝ =>
      (z.1.1, blockRotation n p z.2 * z.1.2) :=
    (continuous_fst.comp continuous_fst).prodMk
      (((continuous_blockRotation n p).comp continuous_snd).mul
        (continuous_snd.comp continuous_fst))
  exact (hF.comp harg).mul (by fun_prop)

private theorem continuous_high_family (S : List (Slot n))
    (F : K n → C(G n ℝ, ℂ)) (hF : Continuous (fun z : K n × G n ℝ => F z.1 z.2)) :
    Continuous fun z : K n × G n ℝ => highModesList S (F z.1) z.2 := by
  induction S with
  | nil => exact hF
  | cons s S ih =>
    simp only [highModesList_cons, highModes_apply_at]
    exact ih.sub (continuous_const.mul (continuous_finsetSum _ fun j _ =>
      continuous_coefficient_family s.p j (fun y => highModesList S (F y)) ih))

private def projectedColumn (ds : List RealBlock) (φ : C(K n, ℂ)) (y : K n) : C(G n ℝ, ℂ) :=
  highModesList (slots ds n) (signFilters ds (List.ofFn id) (continuousColumn φ y))

private theorem continuous_projectedColumn (ds : List RealBlock) (φ : C(K n, ℂ)) :
    Continuous fun z : K n × G n ℝ => projectedColumn ds φ z.1 z.2 := by
  unfold projectedColumn
  refine continuous_high_family (slots ds n)
    (fun y => signFilters ds (List.ofFn id) (continuousColumn φ y)) ?_
  refine continuous_sign_family ds (List.ofFn id) (continuousColumn φ) ?_
  exact φ.continuous.comp
    ((continuous_signedOrthogonalPart.comp continuous_snd).inv.mul continuous_fst)

private theorem norm_signFilters_le (ds : List RealBlock) (I : List (Fin n))
    (F : C(G n ℝ, ℂ)) {a : ℝ} (ha : ∀ x, ‖F x‖ ≤ a) (x : G n ℝ) :
    ‖signFilters ds I F x‖ ≤ a := by
  induction I generalizing x with
  | nil => exact ha x
  | cons i I ih =>
    rw [signFilters_cons, signFilter_apply, norm_mul, norm_inv, Complex.norm_two]
    refine (mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)).trans ?_
    rw [norm_mul, (RealStrictCharacterLanglandsQuotient.isSignedPower ds).norm_neg_one, one_mul]
    have h₁ := ih x
    have h₂ := ih (Unitary.toUnits (signReflection n i) * x)
    linarith

private def highBound (S : List (Slot n)) : ℝ :=
  (S.map fun s => (1 : ℝ) + (lowModes s.M).card).prod

private theorem norm_highModes_le (p m : ℕ) (F : C(G n ℝ, ℂ)) {a : ℝ}
    (ha : ∀ x, ‖F x‖ ≤ a) (x : G n ℝ) :
    ‖highModes p m F x‖ ≤ (1 + ((lowModes m).card : ℝ)) * a := by
  rw [highModes_apply_at, Finset.mul_sum]
  have hj (j : ℤ) :
      ‖(2 * (Real.pi : ℂ))⁻¹ * blockFourierCoefficient n p j F x‖ ≤ a := by
    rw [norm_mul, norm_inv, norm_mul, Complex.norm_two, Complex.norm_real,
      Real.norm_of_nonneg Real.pi_pos.le]
    refine (mul_le_mul_of_nonneg_left (norm_blockFourierCoefficient_le (p := p) j
      (fun θ => ha (blockRotation n p θ * x))) (by positivity)).trans_eq ?_
    rw [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
  calc
    _ ≤ ‖F x‖ + ∑ j ∈ lowModes m,
        ‖(2 * (Real.pi : ℂ))⁻¹ * blockFourierCoefficient n p j F x‖ :=
      (norm_sub_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
    _ ≤ a + ∑ _ ∈ lowModes m, a := add_le_add (ha x) (Finset.sum_le_sum fun j _ => hj j)
    _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]; ring

private theorem norm_highModesList_le (S : List (Slot n))
    (F : C(G n ℝ, ℂ)) {a : ℝ} (ha : ∀ x, ‖F x‖ ≤ a) (x : G n ℝ) :
    ‖highModesList S F x‖ ≤ highBound S * a := by
  induction S generalizing x with
  | nil => simpa [highBound] using ha x
  | cons s S ih =>
    rw [highModesList_cons]
    exact (norm_highModes_le s.p s.M _ ih x).trans_eq (by simp [highBound, mul_assoc])

private def integralKernel (ds : List RealBlock) (g : G n ℝ) : C(K n, ℂ) →ₗ[ℂ] C(K n, ℂ) where
  toFun φ :=
    ⟨fun y => compactWeight ds g y * projectedColumn ds φ y
        (Unitary.toUnits (signedOrthogonalPart (Unitary.toUnits y * g))),
      (compactWeight ds g).continuous.mul ((continuous_projectedColumn ds φ).comp
        (continuous_id.prodMk (continuous_unitary_toUnits.comp
          (continuous_signedOrthogonalPart.comp (continuous_unitary_toUnits.mul continuous_const)))))⟩
  map_add' φ ψ := by
    have h (y : K n) : continuousColumn (φ + ψ) y =
        continuousColumn φ y + continuousColumn ψ y := ContinuousMap.ext fun _ => rfl
    apply ContinuousMap.ext
    intro y
    let x := Unitary.toUnits (signedOrthogonalPart (Unitary.toUnits y * g))
    change compactWeight ds g y * projectedColumn ds (φ + ψ) y x =
      compactWeight ds g y * projectedColumn ds φ y x +
        compactWeight ds g y * projectedColumn ds ψ y x
    simp only [projectedColumn, h, map_add, ContinuousMap.add_apply, mul_add]
  map_smul' c φ := by
    have h (y : K n) : continuousColumn (c • φ) y = c • continuousColumn φ y :=
      ContinuousMap.ext fun _ => rfl
    apply ContinuousMap.ext
    intro y
    let x := Unitary.toUnits (signedOrthogonalPart (Unitary.toUnits y * g))
    change compactWeight ds g y * projectedColumn ds (c • φ) y x =
      c * (compactWeight ds g y * projectedColumn ds φ y x)
    simp only [projectedColumn, h, map_smul, ContinuousMap.smul_apply, smul_eq_mul]
    ring

private theorem norm_integralKernel_le (ds : List RealBlock) (g : G n ℝ) (φ : C(K n, ℂ)) :
    ‖integralKernel ds g φ‖ ≤ (‖compactWeight ds g‖ * highBound (slots ds n)) * ‖φ‖ := by
  have h (y : K n) (x : G n ℝ) :
      ‖projectedColumn ds φ y x‖ ≤ highBound (slots ds n) * ‖φ‖ :=
    norm_highModesList_le _ _ (norm_signFilters_le ds _ _ (fun _ => φ.norm_coe_le_norm _)) x
  have hb : 0 ≤ highBound (slots ds n) * ‖φ‖ := (norm_nonneg _).trans (h 1 1)
  refine (ContinuousMap.norm_le _ (by rw [mul_assoc]; exact mul_nonneg (norm_nonneg _) hb)).2
    fun y => ?_
  change ‖compactWeight ds g y * projectedColumn ds φ y _‖ ≤ _
  rw [norm_mul, mul_assoc]
  exact mul_le_mul ((compactWeight ds g).norm_coe_le_norm y) (h y _) (norm_nonneg _) (norm_nonneg _)

/-- The column integral for an arbitrary continuous compact test. -/
def compactTestTrace (μ : Measure (K n)) (ds : List RealBlock)
    (g : G n ℝ) (φ : C(K n, ℂ)) : ℂ :=
  ∫ y, integralKernel ds g φ y ∂μ

theorem compactTestTrace_apply (μ : Measure (K n)) (ds : List RealBlock)
    (g : G n ℝ) (φ : C(K n, ℂ)) :
    compactTestTrace μ ds g φ = ∫ y,
      extension (shiftedExponent n (realPositionExponent ds)) 1 (Unitary.toUnits y * g) *
        highModesList (slots ds n) (signFilters ds (List.ofFn id) (continuousColumn φ y))
          (Unitary.toUnits (signedOrthogonalPart (Unitary.toUnits y * g))) ∂μ := rfl

theorem continuous_compactTestTrace (μ : Measure (K n)) [μ.IsHaarMeasure]
    (ds : List RealBlock) (g : G n ℝ) : Continuous (compactTestTrace μ ds g) := by
  let L := (integralKernel ds g).mkContinuous _ (norm_integralKernel_le ds g)
  let J := ContinuousMap.toLp (E := ℂ) 1 μ ℂ
  have h : compactTestTrace μ ds g = (fun F : Lp ℂ 1 μ => ∫ y, F y ∂μ) ∘ J ∘ L := by
    funext φ
    exact (integral_congr_ae (ContinuousMap.coeFn_toLp (E := ℂ) (p := 1) (𝕜 := ℂ)
      μ (integralKernel ds g φ))).symm
  rw [h]
  exact continuous_integral.comp (J.continuous.comp L.continuous)

theorem compactTestTrace_eq_averageTrace (μ : Measure (K n)) [μ.IsHaarMeasure]
    {ds : List RealBlock} (hr : realRank ds = n) (g : G n ℝ) (φ : polynomialStar n) :
    compactTestTrace μ ds g φ = averageTrace μ ds φ g := by
  rw [averageTrace_eq_compactProjection_integral μ hr φ g, compactTestTrace]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  change integralKernel ds g φ y = (compactProjection hr (kernelColumn φ y)).1
    (Unitary.toUnits y * g)
  rw [compactProjection_apply]
  have h : filteredPolynomial ds (kernelColumn φ y) = projectedColumn ds φ y := by
    unfold filteredPolynomial projectedColumn
    simp only [LinearMap.comp_apply]
    congr 2
    apply ContinuousMap.ext
    intro x
    change extension 0 (fun k => (φ : C(K n, ℂ)) (k⁻¹ * y)) x =
      (φ : C(K n, ℂ)) ((signedOrthogonalPart x)⁻¹ * y)
    simp [extension, gramExpression]
  rw [h]
  change compactWeight ds g y * projectedColumn ds φ y _ = _
  simp [compactWeight, extension]

/-- Isomorphic real standard modules give equal column integrals for every continuous
compact test. -/
def RealStandardCompactTestTraceStatement : Prop :=
  ∀ (n : ℕ) (μ : Measure (K n)) [μ.IsHaarMeasure] (ds es : List RealBlock),
    realRank ds = n → realRank es = n →
    ∀ T : V n ds →ₗ[ℂ] V n es,
      IsRealStandardIntertwiner n (realStandardRep n es) (realStandardLie n es) ds T →
      Function.Bijective T →
      ∀ g : G n ℝ, compactTestTrace μ ds g = compactTestTrace μ es g

theorem realStandardCompactTestTrace : RealStandardCompactTestTraceStatement := by
  intro n μ _ ds es hd he T hT hbij g
  have hdense : Dense (polynomialStar n : Set C(K n, ℂ)) := by
    rw [dense_iff_closure_eq, ← StarSubalgebra.topologicalClosure_coe,
      ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
        _ polynomialStar_separatesPoints, StarSubalgebra.coe_top]
  refine Continuous.ext_on hdense (continuous_compactTestTrace μ ds g)
    (continuous_compactTestTrace μ es g) ?_
  intro φ hφ
  exact (compactTestTrace_eq_averageTrace μ hd g ⟨φ, hφ⟩).trans
    ((realStandardCompactTrace n μ ds es T hT hbij ⟨φ, hφ⟩ g).trans
      (compactTestTrace_eq_averageTrace μ he g ⟨φ, hφ⟩).symm)

end Langlands.Archimedean.RealStandardCompactAverage
