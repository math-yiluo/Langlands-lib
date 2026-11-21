import Langlands.Global.RankinSelberg.ComplexBruhatChartDerivative

/-! # Variable strictly upper directions in the chart distribution equation -/

noncomputable section

open Set TopologicalSpace
open scoped Classical ContDiff Distributions Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexBruhatVariableDirection

open Langlands.LocalFactor.Archimedean (ComplexCharacterData)
open ComplexOppositeCompactChart (Coordinates)
open ComplexBruhatGaussChart (chartCoordinates chartSection)
open ComplexBruhatTestExtension (ChartTest inducingMultiplier chartUpperMatrix)
open ComplexBruhatChartDerivative (chartVector chartScalar contDiff_chartVector
  chartDerivativeTest chartDerivativeTest_apply)

local notation "Mat" => fun n => Matrix (Fin n) (Fin n) ℂ
variable {n r : ℕ}

private def vectorLinear (w : Equiv.Perm (Fin n)) (z : Coordinates n) : Mat n →ₗ[ℝ] Coordinates n :=
  ((fderiv ℝ (chartCoordinates w) (chartSection w z).val).comp
    (ContinuousLinearMap.mul ℝ (Mat n) (chartSection w z).val)).toLinearMap

private def scalarLinear (w : Equiv.Perm (Fin n)) (ds : List ComplexCharacterData) (z : Coordinates n) :
    Mat n →ₗ[ℝ] ℂ :=
  ((fderiv ℝ (fun A => inducingMultiplier ds (chartUpperMatrix w A)) (chartSection w z).val).comp
    (ContinuousLinearMap.mul ℝ (Mat n) (chartSection w z).val)).toLinearMap

/-- The differential of the trace character is real-linear in the matrix direction. -/
def frequencyLinear (a : ℂˣ) : Mat (r + 1) →ₗ[ℝ] ℂ where
  toFun := complexWhittakerFrequency a
  map_add' X Y := by
    simp only [complexWhittakerFrequency, Matrix.add_apply, Finset.sum_add_distrib, mul_add,
      map_add, Complex.ofReal_add, add_mul]
  map_smul' c X := by
    simp only [complexWhittakerFrequency, Matrix.smul_apply, RingHom.id_apply]
    rw [← Finset.smul_sum, mul_smul_comm, map_smul, smul_eq_mul]
    simp only [Complex.ofReal_mul, Complex.real_smul]
    ring

@[simp] theorem frequencyLinear_apply (a : ℂˣ) (X : Mat (r + 1)) :
    frequencyLinear a X = complexWhittakerFrequency a X := rfl

private def realWeightedTest (c : Coordinates n → ℝ) (hc : ContDiff ℝ ∞ c) (φ : ChartTest n) : ChartTest n := by
  have hC : HasCompactSupport (c • (φ : Coordinates n → ℂ)) := φ.hasCompactSupport.smul_left
  exact ⟨c • (φ : Coordinates n → ℂ), hc.smul φ.contDiff, hC, le_top⟩

private theorem fderiv_realWeightedTest (c : Coordinates n → ℝ) (hc : ContDiff ℝ ∞ c)
    (φ : ChartTest n) (z v : Coordinates n) :
    fderiv ℝ (realWeightedTest c hc φ) z v = c z • fderiv ℝ φ z v + fderiv ℝ c z v • φ z := by
  have hd := ((hc.differentiable (by simp) z).hasFDerivAt.smul (φ.contDiff.differentiable (by simp) z).hasFDerivAt).fderiv
  change fderiv ℝ (c • (φ : Coordinates n → ℂ)) z v = _
  rw [hd]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]

section Expansion

variable {ι : Type*} [Fintype ι]
variable (w : Equiv.Perm (Fin (r + 1))) (ds : List ComplexCharacterData) (a : ℂˣ)
variable (Y : ι → Mat (r + 1)) (c : ι → Coordinates (r + 1) → ℝ)

private def correction (z : Coordinates (r + 1)) : ℝ :=
  ∑ i, fderiv ℝ (c i) z (chartVector w (Y i) z)

private theorem contDiff_correction (hc : ∀ i, ContDiff ℝ ∞ (c i)) :
    ContDiff ℝ ∞ (correction w Y c) :=
  ContDiff.sum fun i _ => ((hc i).fderiv_right (by simp)).clm_apply (contDiff_chartVector w (Y i))

private def residual (hc : ∀ i, ContDiff ℝ ∞ (c i)) (φ : ChartTest (r + 1)) : ChartTest (r + 1) :=
  ∑ i, (chartDerivativeTest w ds (Y i) (realWeightedTest (c i) (hc i) φ) -
    complexWhittakerFrequency a (Y i) • realWeightedTest (c i) (hc i) φ)

set_option maxHeartbeats 850000 in
private theorem residual_eval (hc : ∀ i, ContDiff ℝ ∞ (c i)) (φ : ChartTest (r + 1))
    (z : Coordinates (r + 1)) :
    residual w ds a Y c hc φ z =
      fderiv ℝ φ z (chartVector w (∑ i, c i z • Y i) z) +
        (chartScalar w ds (∑ i, c i z • Y i) z + (correction w Y c z : ℂ) -
          complexWhittakerFrequency a (∑ i, c i z • Y i)) * φ z := by
  let D := fderiv ℝ φ z
  let V := vectorLinear w z
  let B := scalarLinear w ds z
  let F := frequencyLinear a (r := r)
  have hTerms (i : ι) :
      (chartDerivativeTest w ds (Y i) (realWeightedTest (c i) (hc i) φ) -
        complexWhittakerFrequency a (Y i) • realWeightedTest (c i) (hc i) φ) z =
      c i z • D (V (Y i)) +
        (c i z • B (Y i) + (fderiv ℝ (c i) z (V (Y i)) : ℂ) - c i z • F (Y i)) * φ z := by
    change chartDerivativeTest w ds (Y i) (realWeightedTest (c i) (hc i) φ) z -
      complexWhittakerFrequency a (Y i) * (c i z • φ z) = _
    rw [chartDerivativeTest_apply, fderiv_realWeightedTest]
    change c i z • D (V (Y i)) + fderiv ℝ (c i) z (V (Y i)) • φ z + B (Y i) * (c i z • φ z) -
      F (Y i) * (c i z • φ z) = _
    simp only [Complex.real_smul]
    ring
  let Ev : ChartTest (r + 1) →+ ℂ :=
    { toFun := fun f => f z
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  change Ev (∑ i, (chartDerivativeTest w ds (Y i) (realWeightedTest (c i) (hc i) φ) -
      complexWhittakerFrequency a (Y i) • realWeightedTest (c i) (hc i) φ)) = _
  rw [map_sum]
  simp_rw [show ∀ f : ChartTest (r + 1), Ev f = f z from fun _ => rfl, hTerms]
  change (∑ i, (c i z • D (V (Y i)) +
    (c i z • B (Y i) + (fderiv ℝ (c i) z (V (Y i)) : ℂ) - c i z • F (Y i)) * φ z)) =
    D (V (∑ i, c i z • Y i)) + (B (∑ i, c i z • Y i) +
      ((∑ i, fderiv ℝ (c i) z (V (Y i)) : ℝ) : ℂ) - F (∑ i, c i z • Y i)) * φ z
  simp only [map_sum, map_smul, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, Complex.ofReal_sum]

private theorem residual_annihilated (hc : ∀ i, ContDiff ℝ ∞ (c i))
    (T : ChartTest (r + 1) →L[ℂ] ℂ)
    (hT : ∀ i φ, T (chartDerivativeTest w ds (Y i) φ) = complexWhittakerFrequency a (Y i) * T φ)
    (φ : ChartTest (r + 1)) : T (residual w ds a Y c hc φ) = 0 := by
  simp only [residual, map_sum, map_sub, hT, map_smul, smul_eq_mul, sub_self, Finset.sum_const_zero]

end Expansion

private abbrev Entry (n : ℕ) := Fin n × Fin n

private def elementary (p : Entry n × Bool) : Mat n :=
  if p.1.1 < p.1.2 then Matrix.single p.1.1 p.1.2 (if p.2 then Complex.I else 1) else 0

private def coefficient (X : Mat n) (p : Entry n × Bool) : ℝ :=
  if p.2 then (X p.1.1 p.1.2).im else (X p.1.1 p.1.2).re

private theorem elementary_upper (p : Entry n × Bool) (i j : Fin n) (hj : j ≤ i) : elementary p i j = 0 := by
  unfold elementary
  by_cases hp : p.1.1 < p.1.2
  · rw [ite_eq_left hp, Matrix.single_apply, ite_eq_right]
    rintro ⟨hi, hj'⟩
    exact hp.not_ge (hi.symm ▸ hj' ▸ hj)
  · simp only [ite_eq_right hp, Matrix.zero_apply]

private theorem sum_elementary (X : Mat n) (hX : ∀ i j, j ≤ i → X i j = 0) :
    (∑ p : Entry n × Bool, coefficient X p • elementary p) = X := by
  have he (i j : Fin n) :
      (∑ b : Bool, coefficient X ((i, j), b) • elementary ((i, j), b)) = Matrix.single i j (X i j) := by
    by_cases hij : i < j
    · simp only [Fintype.sum_bool, elementary, coefficient, hij, ite_true, Bool.false_eq_true, ite_false,
        Matrix.smul_single, Complex.real_smul, mul_one, ← Matrix.single_add]
      congr 1
      simpa only [add_comm] using Complex.re_add_im (X i j)
    · simp [elementary, hij, hX i j (le_of_not_gt hij)]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp_rw [he]
  exact (Matrix.matrix_eq_sum_single X).symm

/-- A smooth variable strictly upper direction gives a test identity with a real
scalar correction from differentiating its real matrix coefficients. -/
def ComplexBruhatVariableDirectionStatement : Prop :=
  ∀ (r : ℕ) (ds : List ComplexCharacterData) (a : ℂˣ) (w : Equiv.Perm (Fin (r + 1)))
    (T : ChartTest (r + 1) →L[ℂ] ℂ),
    (∀ (Y : Mat (r + 1)), (∀ i j, j ≤ i → Y i j = 0) → ∀ φ : ChartTest (r + 1),
      T (chartDerivativeTest w ds Y φ) = complexWhittakerFrequency a Y * T φ) →
    ∀ (X : Coordinates (r + 1) → Mat (r + 1)), ContDiff ℝ ∞ X → (∀ z i j, j ≤ i → X z i j = 0) →
    ∃ (b : Coordinates (r + 1) → ℝ) (A : ChartTest (r + 1) → ChartTest (r + 1)),
      ContDiff ℝ ∞ b ∧ (∀ φ, T (A φ) = 0) ∧
      ∀ φ z, A φ z = fderiv ℝ φ z (chartVector w (X z) z) +
        (chartScalar w ds (X z) z + (b z : ℂ) - complexWhittakerFrequency a (X z)) * φ z

theorem complexBruhatVariableDirection : ComplexBruhatVariableDirectionStatement := by
  intro r ds a w T hT X hSmooth hX
  let c (p : Entry (r + 1) × Bool) (z : Coordinates (r + 1)) := coefficient (X z) p
  have hc (p : Entry (r + 1) × Bool) : ContDiff ℝ ∞ (c p) := by
    have he := ((Matrix.entryLinearMap ℝ ℂ p.1.1 p.1.2).toContinuousLinearMap.contDiff).comp hSmooth
    change ContDiff ℝ ∞ (fun z => if p.2 then (X z p.1.1 p.1.2).im else (X z p.1.1 p.1.2).re)
    split
    · exact Complex.imCLM.contDiff.comp he
    · exact Complex.reCLM.contDiff.comp he
  refine ⟨correction w elementary c, residual w ds a elementary c hc,
    contDiff_correction w elementary c hc,
    residual_annihilated w ds a elementary c hc T (fun p => hT _ (elementary_upper p)), fun φ z => ?_⟩
  rw [residual_eval w ds a elementary c hc φ z, sum_elementary (X z) (hX z)]

end Langlands.Global.RankinSelbergGlobal.ComplexBruhatVariableDirection
