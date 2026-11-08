import Langlands.Representation.Conductor.SphericalCentral
import Langlands.Representation.Conductor.SphericalLinearity

/-! # Central translation of actual model coefficients -/

noncomputable section

namespace Langlands.Conductor

open MeasureTheory Langlands.GeneralLinear Langlands.Whittaker
open Langlands.GeneralLinear.Iwasawa Langlands.RankinSelberg
open Langlands.QuotientIntegration Langlands.HarmonicAnalysis

universe uF uV

section Translation

variable {F : Type uF} [Field F] [TopologicalSpace F] {n : ℕ}
variable (abv : AbsoluteValue F ℝ)

omit [TopologicalSpace F] in
theorem determinantWeight_mul (g k : Langlands.GeneralLinear (n + 1) F) (s : ℂ) :
    determinantWeight abv (g * k) s =
      determinantWeight abv g s * determinantWeight abv k s := by
  simp only [determinantWeight, Units.val_mul, Matrix.det_mul, map_mul,
    Complex.ofReal_mul]
  exact Complex.mul_cpow_ofReal_nonneg (abv.nonneg _) (abv.nonneg _) s

omit [TopologicalSpace F] in
theorem determinantWeight_ne_zero (g : Langlands.GeneralLinear (n + 1) F) (s : ℂ) :
    determinantWeight abv g s ≠ 0 := by
  apply Complex.cpow_ne_zero_iff.mpr
  apply Or.inl
  exact Complex.ofReal_ne_zero.mpr ((abv.pos (Matrix.GeneralLinearGroup.det_ne_zero g)).ne')

variable {ψ : UnitaryAdditiveCharacter F} {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (π : Representation ℂ (Langlands.GeneralLinear ((n + 1) + 1) F) V)
variable (ℓ : glFunctionals ψ (n + 1) π) (ϖ : Fˣ)

/-- The actual model action of the scalar torus in the smaller general linear group. -/
def corankOneCentralTranslate (t : ℤ) :
    Module.End ℂ (coefficientModel π ℓ).toSubmodule :=
  modelRepresentation π ℓ (rankInclusion 1 (torus ϖ (fun _ : Fin (n + 1) => t)))

@[simp] theorem corankOneCentralTranslate_apply
    (t : ℤ) (w : (coefficientModel π ℓ).toSubmodule)
    (g : Langlands.GeneralLinear ((n + 1) + 1) F) :
    (corankOneCentralTranslate π ℓ ϖ t w).val.val g =
      w.val.val (g * rankInclusion 1 (torus ϖ (fun _ : Fin (n + 1) => t))) := rfl

theorem corankOneCentralTranslate_restriction
    (t : ℤ) (w : (coefficientModel π ℓ).toSubmodule)
    (g : Langlands.GeneralLinear (n + 1) F) :
    (corankOneCentralTranslate π ℓ ϖ t w).val.val (rankInclusion 1 g) =
      w.val.val (rankInclusion 1 (g * torus ϖ (fun _ : Fin (n + 1) => t))) := by
  rw [corankOneCentralTranslate_apply, map_mul]

/-- The scalar determinant weight and the inverse coordinate-product shift
in the central change of variables. -/
def corankOneCentralTranslationFactor (t : ℤ) :
    symmetricTorusSubalgebra (Fin (n + 1)) ℂ :=
  algebraMap ℂ (symmetricTorusSubalgebra (Fin (n + 1)) ℂ)
    (determinantWeight abv (torus ϖ (fun _ : Fin (n + 1) => t)) (0 - 1 / 2))⁻¹ *
      (symmetricTorusDeterminantUnit (Fin (n + 1)) ℂ ^ (-t) :
        (symmetricTorusSubalgebra (Fin (n + 1)) ℂ)ˣ)

variable [ValuativeRel F] {ϖ : Fˣ}
variable (hϖ : IsUniformizingElement (ValuativeRel.valuation F) ϖ) (q : ℕ)
variable (hψ : ∀ x ∈ (ValuativeRel.valuation F).integer, ψ x = 1)

include hψ in
theorem corankOnePolynomialFunction_centralTranslate
    (t : ℤ) (w : (coefficientModel π ℓ).toSubmodule)
    (g : Langlands.GeneralLinear (n + 1) F) :
    corankOnePolynomialFunction ψ abv hϖ q
      (corankOneCentralTranslate π ℓ ϖ t w).val g =
      corankOneCentralTranslationFactor abv ϖ t *
        corankOnePolynomialFunction ψ abv hϖ q w.val
          (g * torus ϖ (fun _ : Fin (n + 1) => t)) := by
  apply symmetricTorus_eq_of_evaluations
  intro x
  simp only [corankOnePolynomialFunction, corankOneCentralTranslate_restriction,
    determinantWeight_mul, sphericalWhittakerPolynomial_mul_torus_const hϖ _ q
      (isIntegrallyTrivial_inverseStandardCharacter hψ n),
    corankOneCentralTranslationFactor, map_mul, map_smul, AlgHom.commutes,
    algHom_apply_unit_zpow, symmetricTorusEvaluation_determinantUnit,
    Algebra.algebraMap_self, RingHom.id_apply, smul_eq_mul,
    Units.val_zpow_eq_zpow_val]
  simp only [zpow_neg]
  have hD := determinantWeight_ne_zero abv
    (torus ϖ (fun _ : Fin (n + 1) => t)) (-1 / 2)
  have hU : ((∏ i : Fin (n + 1), x i : ℂˣ) : ℂ) ^ t ≠ 0 :=
    zpow_ne_zero _ (Units.ne_zero _)
  field_simp [hD, hU]

theorem sphericalQuotientDegree_rightTranslate_torus_const
    [IsTopologicalGroup (Langlands.GeneralLinear (n + 1) F)]
    (t : ℤ) (a : LeftUnipotentQuotient n F) :
    sphericalQuotientDegree hϖ
      (rightTranslate (upperUnipotent (n + 1) F)
        (torus ϖ (fun _ : Fin (n + 1) => t)) a) =
      sphericalQuotientDegree hϖ a + (n + 1 : ℕ) * t := by
  induction a using Quotient.inductionOn with
  | h g =>
      simp only [rightTranslate_mk, sphericalQuotientDegree_mk,
        exponent_mul_torus_const, Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem corankOnePolynomialIntegrand_centralTranslate
    [IsTopologicalGroup (Langlands.GeneralLinear (n + 1) F)]
    (t : ℤ) (w : (coefficientModel π ℓ).toSubmodule)
    (a : LeftUnipotentQuotient n F) :
    corankOnePolynomialIntegrand ψ abv hϖ q
      (corankOneCentralTranslate π ℓ ϖ t w).val hψ a =
      corankOneCentralTranslationFactor abv ϖ t *
        corankOnePolynomialIntegrand ψ abv hϖ q w.val hψ
          (rightTranslate (upperUnipotent (n + 1) F)
            (torus ϖ (fun _ : Fin (n + 1) => t)) a) := by
  induction a using Quotient.inductionOn with
  | h g => exact corankOnePolynomialFunction_centralTranslate abv π ℓ hϖ q hψ t w g

theorem degreeCorankOnePolynomialIntegrand_centralTranslate
    [IsTopologicalGroup (Langlands.GeneralLinear (n + 1) F)]
    (t : ℤ) (w : (coefficientModel π ℓ).toSubmodule)
    (d : ℤ) (a : LeftUnipotentQuotient n F) :
    degreeCorankOnePolynomialIntegrand ψ abv hϖ q
      (corankOneCentralTranslate π ℓ ϖ t w).val hψ d a =
      corankOneCentralTranslationFactor abv ϖ t *
        degreeCorankOnePolynomialIntegrand ψ abv hϖ q w.val hψ
          (d + (n + 1 : ℕ) * t)
          (rightTranslate (upperUnipotent (n + 1) F)
            (torus ϖ (fun _ : Fin (n + 1) => t)) a) := by
  classical
  simp only [degreeCorankOnePolynomialIntegrand,
    sphericalQuotientDegree_rightTranslate_torus_const, add_left_inj]
  split_ifs
  · exact corankOnePolynomialIntegrand_centralTranslate abv π ℓ hϖ q hψ t w a
  · exact (mul_zero _).symm

end Translation

section Model

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable [IsNonarchimedeanLocalField F] {n : ℕ}
variable [MeasurableSpace (Langlands.GeneralLinear (n + 1) F)]
  [BorelSpace (Langlands.GeneralLinear (n + 1) F)]
variable [MeasurableSpace (upperUnipotent (n + 1) F)]
  [BorelSpace (upperUnipotent (n + 1) F)]
variable [MeasurableSpace (LeftUnipotentQuotient n F)]
  [MeasurableSpace (LeftUnipotentQuotient 0 F)]
variable {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ}
variable {ϖ : Fˣ} {μ : Measure (LeftUnipotentQuotient n F)}
variable (h : IsJacquetNormalization q ψ abv ϖ μ)
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (π : Representation ℂ (Langlands.GeneralLinear ((n + 1) + 1) F) V)
variable (hπ : IsSmooth π) (ℓ : glFunctionals ψ (n + 1) π)

private theorem modelCoefficient_evaluation_as_integral
    (w : (coefficientModel π ℓ).toSubmodule)
    (x : Fin (n + 1) → ℂˣ) (d : ℤ) :
    symmetricTorusEvaluation (Fin (n + 1)) ℂ x
      (degreeCorankOneModelCoefficient h π hπ ℓ w d) =
    ∫ a, symmetricTorusEvaluation (Fin (n + 1)) ℂ x
      (degreeCorankOneModelIntegrand h π ℓ w d a) ∂μ := by
  simpa only [degreeCorankOneModelIntegrand,
    symmetricTorusEvaluation_degreeCorankOnePolynomialIntegrand] using
    symmetricTorusEvaluation_degreeCorankOneModelCoefficient h π hπ ℓ w x d

/-- Central translation of the actual integrated coefficient. The quotient
change of variables uses the right invariance of the Jacquet measure. -/
theorem degreeCorankOneModelCoefficient_centralTranslate
    (t : ℤ) (w : (coefficientModel π ℓ).toSubmodule) (d : ℤ) :
    degreeCorankOneModelCoefficient h π hπ ℓ
      (corankOneCentralTranslate π ℓ ϖ t w) d =
      corankOneCentralTranslationFactor abv ϖ t *
        degreeCorankOneModelCoefficient h π hπ ℓ w (d + (n + 1 : ℕ) * t) := by
  let : BorelSpace (LeftUnipotentQuotient n F) := h.borel
  apply symmetricTorus_eq_of_evaluations
  intro x
  rw [map_mul]
  simp_rw [modelCoefficient_evaluation_as_integral]
  have he (a : LeftUnipotentQuotient n F) :
      degreeCorankOneModelIntegrand h π ℓ
        (corankOneCentralTranslate π ℓ ϖ t w) d a =
      corankOneCentralTranslationFactor abv ϖ t *
        degreeCorankOneModelIntegrand h π ℓ w (d + (n + 1 : ℕ) * t)
          (rightTranslate (upperUnipotent (n + 1) F)
            (torus ϖ (fun _ : Fin (n + 1) => t)) a) :=
    degreeCorankOnePolynomialIntegrand_centralTranslate abv π ℓ h.uniformizer q
      h.conductor.1 t w d a
  simp_rw [he, map_mul]
  rw [integral_const_mul]
  rw [(h.measure.right_invariant (torus ϖ (fun _ : Fin (n + 1) => t))).integral_comp
    (rightTranslate (upperUnipotent (n + 1) F)
      (torus ϖ (fun _ : Fin (n + 1) => t))).measurableEmbedding
        (fun a => symmetricTorusEvaluation (Fin (n + 1)) ℂ x
          (degreeCorankOneModelIntegrand h π ℓ w (d + (n + 1 : ℕ) * t) a))]

end Model

end Langlands.Conductor
