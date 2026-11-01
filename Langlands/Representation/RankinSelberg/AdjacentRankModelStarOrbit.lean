import Langlands.Representation.RankinSelberg.AdjacentRankModelConvergenceProof
import Langlands.Representation.Whittaker.DualTransform

/-!
# Coefficients and determinant weights on adjacent-rank right orbits

The two unipotent characters in the model-star computation have opposite
signs. The coefficient representation and the additive character stay fixed.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear TensorProduct

universe uF uV

section Algebra

variable {F : Type uF} [Field F] [TopologicalSpace F]

/-- The scalar determinant factor in the inner adjacent-rank integral. -/
def adjacentRankOrbitWeight (abv : AbsoluteValue F ℝ) (χ : Quasicharacter F)
    {n : ℕ} (h : GeneralLinear n F) (s : ℂ) : ℂ :=
  (χ (determinant h) : ℂ) * determinantWeight abv h s

omit [TopologicalSpace F] in
/-- Right multiplication by an upper-unipotent element preserves the determinant. -/
theorem adjacentRank_determinant_right_unipotent {n : ℕ}
    (h : GeneralLinear n F) (u : upperUnipotent n F) :
    determinant (h * u.val) = determinant h := by
  have hu : determinant u.val = 1 := by
    apply Units.ext
    exact unipotent_det u
  rw [map_mul, hu, mul_one]

omit [TopologicalSpace F] in
/-- The determinant weight is constant on right-unipotent orbits. -/
theorem adjacentRank_determinantWeight_right_unipotent (abv : AbsoluteValue F ℝ)
    {n : ℕ} (h : GeneralLinear n F) (u : upperUnipotent n F) (s : ℂ) :
    determinantWeight abv (h * u.val) s = determinantWeight abv h s := by
  simp [determinantWeight, Matrix.det_mul]

/-- The full scalar factor is constant on right-unipotent orbits. -/
theorem adjacentRankOrbitWeight_right_unipotent (abv : AbsoluteValue F ℝ)
    (χ : Quasicharacter F) {n : ℕ} (h : GeneralLinear n F)
    (u : upperUnipotent n F) (s : ℂ) :
    adjacentRankOrbitWeight abv χ (h * u.val) s =
      adjacentRankOrbitWeight abv χ h s := by
  rw [adjacentRankOrbitWeight, adjacentRank_determinant_right_unipotent,
    adjacentRank_determinantWeight_right_unipotent, adjacentRankOrbitWeight]

omit [TopologicalSpace F] in
/-- The determinant at the reflected base point `b = iota(h) * w`. -/
theorem adjacentRank_determinant_reflected_base {n : ℕ} (h : GeneralLinear n F) :
    determinant (inverseTranspose n F h * weylLong n F) =
      determinant (weylLong n F) * (determinant h)⁻¹ := by
  have hi : determinant (inverseTranspose n F h) = (determinant h)⁻¹ := by
    apply Units.ext
    change Matrix.det (inverseTranspose n F h).val = _
    rw [inverseTranspose_coe, Matrix.det_transpose]
    exact congrArg Units.val (map_inv determinant h)
  rw [map_mul, hi, mul_comm]

omit [TopologicalSpace F] in
/-- The unsigned long Weyl matrix has absolute determinant one. -/
theorem adjacentRank_abv_det_weylLong (abv : AbsoluteValue F ℝ) (n : ℕ) :
    abv (Matrix.det (weylLong n F).val) = 1 := by
  have hs : abv (Matrix.det (weylLong n F).val) *
      abv (Matrix.det (weylLong n F).val) = 1 := by
    rw [← map_mul, ← Matrix.det_mul]
    change abv (Matrix.det (weylLong n F * weylLong n F).val) = 1
    rw [weylLong_mul_self]
    simp
  nlinarith [abv.nonneg (Matrix.det (weylLong n F).val)]

omit [TopologicalSpace F] in
/-- Reflection inverts the absolute determinant at the base point. -/
theorem adjacentRank_abv_det_reflected_base (abv : AbsoluteValue F ℝ)
    {n : ℕ} (h : GeneralLinear n F) :
    abv (Matrix.det (inverseTranspose n F h * weylLong n F).val) =
      (abv (Matrix.det h.val))⁻¹ := by
  change abv (determinant (inverseTranspose n F h * weylLong n F) : F) = _
  rw [adjacentRank_determinant_reflected_base, Units.val_mul, map_mul,
    Units.val_inv_eq_inv_val, map_inv₀]
  change abv (Matrix.det (weylLong n F).val) *
    (abv (Matrix.det h.val))⁻¹ = _
  rw [adjacentRank_abv_det_weylLong, one_mul]

omit [TopologicalSpace F] in
/-- The reflected determinant weight has the opposite exponent. -/
theorem adjacentRank_determinantWeight_reflected_base (abv : AbsoluteValue F ℝ)
    {n : ℕ} (h : GeneralLinear n F) (s : ℂ) :
    determinantWeight abv (inverseTranspose n F h * weylLong n F) s =
      determinantWeight abv h (-s) := by
  unfold determinantWeight
  rw [adjacentRank_abv_det_reflected_base, Complex.ofReal_inv,
    Complex.inv_cpow, Complex.cpow_neg]
  rw [Complex.arg_ofReal_of_nonneg (abv.nonneg _)]
  exact Real.pi_ne_zero.symm

/-- Character inversion at the reflected base point. -/
theorem adjacentRank_inverse_character_reflected_base (χ : Quasicharacter F)
    {n : ℕ} (h : GeneralLinear n F) :
    ((χ⁻¹) (determinant (inverseTranspose n F h * weylLong n F)) : ℂ) =
      ((χ⁻¹) (determinant (weylLong n F)) : ℂ) * (χ (determinant h) : ℂ) := by
  rw [adjacentRank_determinant_reflected_base, map_mul, Units.val_mul]
  congr 1
  change (((χ ((determinant h)⁻¹))⁻¹ : ℂˣ) : ℂ) = _
  rw [map_inv, inv_inv]

/-- The scalar factor at the reflected base point, with the inverse character. -/
theorem adjacentRankOrbitWeight_reflected_base (abv : AbsoluteValue F ℝ)
    (χ : Quasicharacter F) {n : ℕ} (h : GeneralLinear n F) (s : ℂ) :
    adjacentRankOrbitWeight abv χ⁻¹ (inverseTranspose n F h * weylLong n F) s =
      ((χ⁻¹) (determinant (weylLong n F)) : ℂ) *
        adjacentRankOrbitWeight abv χ h (-s) := by
  unfold adjacentRankOrbitWeight
  rw [adjacentRank_inverse_character_reflected_base,
    adjacentRank_determinantWeight_reflected_base, mul_assoc]

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ψ : UnitaryAdditiveCharacter F) {r : ℕ}
  (σ : Representation ℂ (GeneralLinear (r + 1) F) V)
  (ℓ : glFunctionals ψ r σ)

/-- Along the source right orbit, inversion gives the inverse standard character. -/
theorem adjacentRank_coefficient_right_orbit
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule)
    (h : GeneralLinear (r + 1) F) (u : upperUnipotent (r + 1) F) :
    glModelFunction ψ r σ ℓ W (h * u.val)⁻¹ =
      ((standardCharacter ψ r u : ℂ)⁻¹) * glModelFunction ψ r σ ℓ W h⁻¹ := by
  simpa only [mul_inv_rev, ← Subgroup.coe_inv, map_inv, Units.val_inv_eq_inv_val] using
    glModelFunction_equivariance ψ r σ ℓ W u⁻¹ h⁻¹

/-- The transformed coefficient on the reflected right orbit has the standard
character and the original coefficient at `h⁻¹`. -/
theorem adjacentRank_coefficient_reflected_right_orbit
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule)
    (h : GeneralLinear (r + 1) F) (u : upperUnipotent (r + 1) F) :
    glModelFunction ψ r σ ℓ W
        (weylLong (r + 1) F *
          inverseTranspose (r + 1) F
            ((inverseTranspose (r + 1) F h * weylLong (r + 1) F) * u.val)⁻¹) =
      (standardCharacter ψ r u : ℂ) * glModelFunction ψ r σ ℓ W h⁻¹ := by
  have ha : weylLong (r + 1) F *
      inverseTranspose (r + 1) F
        ((inverseTranspose (r + 1) F h * weylLong (r + 1) F) * u.val)⁻¹ =
      (reflectedUnipotent u⁻¹).val * h⁻¹ := by
    simp [mul_inv_rev, map_mul, map_inv, reflectedUnipotent_val, mul_assoc]
  rw [ha, glModelFunction_equivariance, standardCharacter_reflected]
  change (((standardCharacter ψ r u⁻¹)⁻¹ : ℂˣ) : ℂ) * _ = _
  rw [map_inv, inv_inv]

end Algebra

section CanonicalTopology

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance modelStarOrbitTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance modelStarOrbitValuative : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance modelStarOrbitLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance modelStarOrbitT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2

/-- Continuity of the exact scalar factor on every canonical p-adic GL. -/
theorem continuous_adjacentRankOrbitWeight (χ : Quasicharacter F.Carrier)
    (n : ℕ) (s : ℂ) :
    Continuous (fun h : GeneralLinear n F.Carrier =>
      adjacentRankOrbitWeight (normalizedAbsoluteValue F.canonicalTopologicalData) χ h s) :=
  (Units.continuous_val.comp
    (χ.continuous.comp determinantContinuous.continuous)).mul
      (continuous_adjacentRank_determinantWeight F n s)

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The original pure integrand is continuous with compact support. -/
theorem adjacentRankPure_weighted_regularity
    (ψ : UnitaryAdditiveCharacter F.Carrier) (r : ℕ)
    (σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hσ : IsSmooth σ) (ℓ : glFunctionals ψ r σ) (χ : Quasicharacter F.Carrier)
    (Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F.Carrier))
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule) (s : ℂ) :
    Continuous (fun h : GeneralLinear (r + 1) F.Carrier =>
      Φ (adjacentRankKernelMatrix h) * glModelFunction ψ r σ ℓ W h⁻¹ *
        (χ (determinant h) : ℂ) *
        determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) h s) ∧
    HasCompactSupport (fun h : GeneralLinear (r + 1) F.Carrier =>
      Φ (adjacentRankKernelMatrix h) * glModelFunction ψ r σ ℓ W h⁻¹ *
        (χ (determinant h) : ℂ) *
        determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) h s) := by
  constructor
  · have hχ : Continuous (fun h : GeneralLinear (r + 1) F.Carrier =>
        (χ (determinant h) : ℂ)) :=
      Units.continuous_val.comp (χ.continuous.comp determinantContinuous.continuous)
    exact ((((SchwartzBruhat.continuous Φ).comp (continuous_adjacentRankKernelMatrix F r)).mul
      ((glModelFunction_continuous ψ r σ hσ ℓ W).comp continuous_inv)).mul hχ).mul
        (continuous_adjacentRank_determinantWeight F _ _)
  · exact ((adjacentRankPure_hasCompactSupport F ψ r σ hσ ℓ Φ W).mul_right).mul_right

end CanonicalTopology

end Langlands.RankinSelberg
