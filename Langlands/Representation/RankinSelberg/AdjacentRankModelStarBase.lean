import Langlands.Representation.RankinSelberg.AdjacentRankModelStarIntegration
import Langlands.Representation.RankinSelberg.AdjacentRankModelStarOrbit
import Langlands.Representation.RankinSelberg.AdjacentRankModelStarRegularity
import Langlands.Representation.RankinSelberg.AdjacentRankModelStarReduction
import Langlands.Representation.RankinSelberg.AdjacentRankModelStarFourierOrbit
import Langlands.HarmonicAnalysis.AdjacentRankUnipotentFourierProof

/-! The fixed-action adjacent-rank model-star identity at the base ambient point. -/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker TensorProduct GeneralLinear Matrix

universe uF uV

section Algebra

variable {F : Type uF} [Field F]

/-- The ambient point at which the scalar unipotent Fourier theorem applies. -/
def adjacentRankModelStarBasePoint (r : ℕ) : GeneralLinear (r + 2) F :=
  weylLong (r + 2) F * adjacentRankZeta F r

/-- The ambient base point and the inner long Weyl element have the same
determinant. -/
theorem adjacentRankModelStarBasePoint_determinant (r : ℕ) :
    determinant (adjacentRankModelStarBasePoint (F := F) r) =
      determinant (weylLong (r + 1) F) := by
  have hz : determinant (adjacentRankZeta F r) = (-1 : Fˣ) ^ (r + 1) := by
    apply Units.ext
    exact adjacentRankZeta_det F r
  rw [adjacentRankModelStarBasePoint, map_mul,
    RankOneGammaTwist.determinant_weylLong_succ, hz]
  calc
    ((-1 : Fˣ) ^ (r + 1) * determinant (weylLong (r + 1) F)) * (-1) ^ (r + 1) =
        ((-1 : Fˣ) ^ (r + 1) * (-1) ^ (r + 1)) *
          determinant (weylLong (r + 1) F) := by ac_rfl
    _ = determinant (weylLong (r + 1) F) := by rw [← mul_pow]; simp

/-- The determinant weight of the ambient base point is one. -/
theorem adjacentRankModelStarBasePoint_weight (abv : AbsoluteValue F ℝ)
    (r : ℕ) (s : ℂ) :
    determinantWeight abv (adjacentRankModelStarBasePoint (F := F) r) s = 1 := by
  unfold determinantWeight
  change (abv (determinant (adjacentRankModelStarBasePoint (F := F) r) : F) : ℂ) ^ s = _
  rw [adjacentRankModelStarBasePoint_determinant]
  change (abv (Matrix.det (weylLong (r + 1) F).val) : ℂ) ^ s = _
  rw [adjacentRank_abv_det_weylLong]
  simp

/-- Complex determinant weights add exponents because the absolute determinant
is nonzero. -/
theorem adjacentRankModelStar_weight_add (abv : AbsoluteValue F ℝ)
    {n : ℕ} (h : GeneralLinear n F) (s t : ℂ) :
    determinantWeight abv h (s + t) =
      determinantWeight abv h s * determinantWeight abv h t :=
  Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (abv.ne_zero h.det_ne_zero))

/-- The row-change and full Fourier factors leave the reflected inner weight. -/
theorem adjacentRankModelStar_weight_balance (abv : AbsoluteValue F ℝ)
    {r : ℕ} (h : GeneralLinear (r + 1) F) :
    determinantWeight abv h ((r : ℂ) / 2) * determinantWeight abv h 1 *
        determinantWeight abv h (-((r + 1 : ℕ) : ℂ)) =
      determinantWeight abv h (-((r : ℂ) / 2)) := by
  rw [← adjacentRankModelStar_weight_add, ← adjacentRankModelStar_weight_add]
  congr 1
  push_cast
  ring

variable [TopologicalSpace F]

/-- The model prefactor cancels the character constant from the orbit
comparison. -/
theorem adjacentRankModelStarBasePoint_prefactor (abv : AbsoluteValue F ℝ)
    (χ : Quasicharacter F) (r : ℕ) (s : ℂ) :
    (χ (determinant (adjacentRankModelStarBasePoint (F := F) r)) : ℂ) *
        determinantWeight abv (adjacentRankModelStarBasePoint (F := F) r) s *
        (χ (determinant (weylLong (r + 1) F)) : ℂ) = 1 := by
  rw [adjacentRankModelStarBasePoint_determinant, adjacentRankModelStarBasePoint_weight,
    mul_one, ← Units.val_mul, ← map_mul, ← map_mul, weylLong_mul_self]
  simp

end Algebra

section CanonicalTopology

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance modelStarBaseTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance modelStarBaseValuative : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance modelStarBaseLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance modelStarBaseT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance modelStarBaseMeasurable : MeasurableSpace F.Carrier := borel _
local instance modelStarBaseBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance modelStarBaseDisconnected : TotallyDisconnectedSpace F.Carrier := by
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance modelStarBaseGLMeasurable (r : ℕ) :
    MeasurableSpace (GeneralLinear (r + 1) F.Carrier) := borel _
local instance modelStarBaseGLBorel (r : ℕ) :
    BorelSpace (GeneralLinear (r + 1) F.Carrier) := ⟨rfl⟩
local instance modelStarBaseUnipotentMeasurable (r : ℕ) :
    MeasurableSpace (upperUnipotent (r + 1) F.Carrier) := borel _
local instance modelStarBaseUnipotentBorel (r : ℕ) :
    BorelSpace (upperUnipotent (r + 1) F.Carrier) := ⟨rfl⟩

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
  (hself : IsSelfDual ψ ν) {r : ℕ}
  (σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
  (hσ : IsSmooth σ) (ℓ : glFunctionals ψ r σ) (χ : Quasicharacter F.Carrier)

/-- The scalar Fourier theorem compares the source orbit at `h` with the
target orbit at `iota(h) * w`, retaining the Weyl character constant. -/
theorem adjacentRankModelStar_pure_right_averages
    (Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F.Carrier))
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule)
    (h : GeneralLinear (r + 1) F.Carrier) :
    (∫ u : upperUnipotent (r + 1) F.Carrier,
      adjacentRankModelStarSourceFunction ψ σ ℓ
        (normalizedAbsoluteValue F.canonicalTopologicalData) χ ((r : ℂ) / 2)
        (adjacentRankRho0 ψ ν hself σ ℓ
          (adjacentRankModelStarBasePoint (F := F.Carrier) r) (Φ ⊗ₜ W))
        (h * u.val) ∂unipotentHaar F.Carrier r) =
      (χ (determinant (weylLong (r + 1) F.Carrier)) : ℂ) *
        ∫ u : upperUnipotent (r + 1) F.Carrier,
          adjacentRankModelStarTargetFunction ψ σ ℓ
            (normalizedAbsoluteValue F.canonicalTopologicalData) χ ((r : ℂ) / 2)
            (adjacentRankFullFourier F ψ ν hself σ ℓ (Φ ⊗ₜ W))
            ((inverseTranspose (r + 1) F.Carrier h * weylLong (r + 1) F.Carrier) *
              u.val) ∂unipotentHaar F.Carrier r := by
  let φ := adjacentRankRowTranslate h
    ((partialFourierEquiv ψ ν (r + 1) hself).symm Φ)
  let L : upperUnipotent (r + 1) F.Carrier → ℂ := fun u =>
    partialFourierEquiv ψ ν (r + 1) hself
      (rectangularTranslate (adjacentRankModelStarBasePoint (F := F.Carrier) r) φ)
      (rectangularJoin u.val.val (adjacentRankEpsilon F.Carrier r)) *
        (inverseStandardCharacter ψ r u : ℂ)
  let R : upperUnipotent (r + 1) F.Carrier → ℂ := fun u =>
    rectangularFourierEquiv ψ ν (r + 1) (r + 2) hself
      (partialFourierEquiv ψ ν (r + 1) hself φ)
      (rectangularJoin ((weylLong (r + 1) F.Carrier).val * u.val.val)
        ((weylLong (r + 1) F.Carrier).val *ᵥ adjacentRankEpsilon F.Carrier r)) *
          (standardCharacter ψ r u : ℂ)
  let A := glModelFunction ψ r σ ℓ W h⁻¹ * (χ (determinant h) : ℂ) *
    determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) h ((r : ℂ) / 2) *
    determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) h 1
  have hL (u : upperUnipotent (r + 1) F.Carrier) :
      adjacentRankModelStarSourceFunction ψ σ ℓ
        (normalizedAbsoluteValue F.canonicalTopologicalData) χ ((r : ℂ) / 2)
        (adjacentRankRho0 ψ ν hself σ ℓ
          (adjacentRankModelStarBasePoint (F := F.Carrier) r) (Φ ⊗ₜ W)) (h * u.val) =
        A * L u := by
    simp only [adjacentRankModelStarSourceFunction, adjacentRankRho0_tmul,
      adjacentRankTestEvaluation_tmul]
    rw [adjacentRank_rho0_kernel_right_orbit F ψ ν hself,
      adjacentRank_coefficient_right_orbit ψ σ ℓ,
      adjacentRank_determinant_right_unipotent,
      adjacentRank_determinantWeight_right_unipotent]
    dsimp only [A, L, φ]
    simp only [inverseStandardCharacter_apply, standardCharacter_apply]
    ring
  have hc : (χ (determinant (weylLong (r + 1) F.Carrier)) : ℂ) *
      ((χ⁻¹) (determinant (weylLong (r + 1) F.Carrier)) : ℂ) = 1 := by
    change ((χ (determinant (weylLong (r + 1) F.Carrier)) : ℂˣ) : ℂ) *
      (((χ (determinant (weylLong (r + 1) F.Carrier)))⁻¹ : ℂˣ) : ℂ) = 1
    rw [← Units.val_mul, mul_inv_cancel]
    rfl
  have hR (u : upperUnipotent (r + 1) F.Carrier) :
      A * R u =
        (χ (determinant (weylLong (r + 1) F.Carrier)) : ℂ) *
          adjacentRankModelStarTargetFunction ψ σ ℓ
            (normalizedAbsoluteValue F.canonicalTopologicalData) χ ((r : ℂ) / 2)
            (adjacentRankFullFourier F ψ ν hself σ ℓ (Φ ⊗ₜ W))
            ((inverseTranspose (r + 1) F.Carrier h * weylLong (r + 1) F.Carrier) *
              u.val) := by
    simp only [adjacentRankModelStarTargetFunction, adjacentRankFullFourier_tmul,
      adjacentRankTestEvaluation_tmul]
    rw [adjacentRank_coefficient_reflected_right_orbit ψ σ ℓ,
      adjacentRank_determinant_right_unipotent,
      adjacentRank_determinantWeight_right_unipotent,
      adjacentRank_inverse_character_reflected_base,
      adjacentRank_determinantWeight_reflected_base]
    dsimp only [A, R, φ]
    rw [adjacentRank_fullFourier_kernel_reflected_orbit F ψ ν hself]
    calc
      _ = (determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData)
          h ((r : ℂ) / 2) *
        determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) h 1 *
        determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData)
          h (-((r + 1 : ℕ) : ℂ))) *
        (glModelFunction ψ r σ ℓ W h⁻¹ * (χ (determinant h) : ℂ) *
          rectangularFourierEquiv ψ ν (r + 1) (r + 2) hself Φ
            (adjacentRankKernelMatrix
              ((inverseTranspose (r + 1) F.Carrier h * weylLong (r + 1) F.Carrier) *
                u.val)) * (standardCharacter ψ r u : ℂ)) := by ring
      _ = _ := by
        rw [adjacentRankModelStar_weight_balance]
        calc
          _ = ((χ (determinant (weylLong (r + 1) F.Carrier)) : ℂ) *
              ((χ⁻¹) (determinant (weylLong (r + 1) F.Carrier)) : ℂ)) *
            (rectangularFourierEquiv ψ ν (r + 1) (r + 2) hself Φ
              (adjacentRankKernelMatrix
                ((inverseTranspose (r + 1) F.Carrier h * weylLong (r + 1) F.Carrier) *
                  u.val)) *
              ((standardCharacter ψ r u : ℂ) * glModelFunction ψ r σ ℓ W h⁻¹) *
              (χ (determinant h) : ℂ) *
              determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData)
                h (-((r : ℂ) / 2))) := by rw [hc, one_mul]; ring
          _ = _ := by ring
  have he : (∫ u, L u ∂unipotentHaar F.Carrier r) =
      ∫ u, R u ∂unipotentHaar F.Carrier r :=
    (adjacentRankUnipotentFourier p F ψ ν hself r φ).2.2
  simp_rw [hL]
  rw [integral_const_mul, he, ← integral_const_mul]
  simp_rw [hR]
  exact integral_const_mul _ _

include hσ in
/-- The pure-tensor integral comparison extends by actual integrability to all
test tensors, after which the base prefactor cancels the Weyl scalar. -/
theorem adjacentRankModelStarBase_of_pure_integrals
    (hpure : ∀
      (Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F.Carrier))
      (W : (glCoefficientModel ψ r σ ℓ).toSubmodule),
      (∫ h, adjacentRankModelStarSourceFunction ψ σ ℓ
        (normalizedAbsoluteValue F.canonicalTopologicalData) χ ((r : ℂ) / 2)
        (adjacentRankRho0 ψ ν hself σ ℓ
          (adjacentRankModelStarBasePoint (F := F.Carrier) r) (Φ ⊗ₜ W)) h
        ∂generalLinearHaar F.Carrier r) =
      (χ (determinant (weylLong (r + 1) F.Carrier)) : ℂ) *
        ∫ h, adjacentRankModelStarTargetFunction ψ σ ℓ
          (normalizedAbsoluteValue F.canonicalTopologicalData) χ ((r : ℂ) / 2)
          (adjacentRankFullFourier F ψ ν hself σ ℓ (Φ ⊗ₜ W)) h
          ∂generalLinearHaar F.Carrier r) :
    AdjacentRankBaseModelStarIdentity F ψ ν hself σ ℓ χ := by
  have hall (Ψ : adjacentRankTestSpace ψ σ ℓ) :
      (∫ h, adjacentRankModelStarSourceFunction ψ σ ℓ
        (normalizedAbsoluteValue F.canonicalTopologicalData) χ ((r : ℂ) / 2)
        (adjacentRankRho0 ψ ν hself σ ℓ
          (adjacentRankModelStarBasePoint (F := F.Carrier) r) Ψ) h
        ∂generalLinearHaar F.Carrier r) =
      (χ (determinant (weylLong (r + 1) F.Carrier)) : ℂ) *
        ∫ h, adjacentRankModelStarTargetFunction ψ σ ℓ
          (normalizedAbsoluteValue F.canonicalTopologicalData) χ ((r : ℂ) / 2)
          (adjacentRankFullFourier F ψ ν hself σ ℓ Ψ) h
          ∂generalLinearHaar F.Carrier r := by
    induction Ψ using adjacentRankTestSpace_induction ψ σ ℓ with
    | tmul Φ W => exact hpure Φ W
    | add Ψ₁ Ψ₂ h₁ h₂ =>
      have hf₁ := adjacentRankModelStarSourceFunction_regularity F ψ r σ hσ ℓ χ
        ((r : ℂ) / 2) (adjacentRankRho0 ψ ν hself σ ℓ
          (adjacentRankModelStarBasePoint (F := F.Carrier) r) Ψ₁)
      have hf₂ := adjacentRankModelStarSourceFunction_regularity F ψ r σ hσ ℓ χ
        ((r : ℂ) / 2) (adjacentRankRho0 ψ ν hself σ ℓ
          (adjacentRankModelStarBasePoint (F := F.Carrier) r) Ψ₂)
      have hq₁ := adjacentRankModelStarTargetFunction_regularity F ψ r σ hσ ℓ χ
        ((r : ℂ) / 2) (adjacentRankFullFourier F ψ ν hself σ ℓ Ψ₁)
      have hq₂ := adjacentRankModelStarTargetFunction_regularity F ψ r σ hσ ℓ χ
        ((r : ℂ) / 2) (adjacentRankFullFourier F ψ ν hself σ ℓ Ψ₂)
      simp only [map_add, adjacentRankModelStarSourceFunction_add,
        adjacentRankModelStarTargetFunction_add, Pi.add_apply]
      rw [integral_add (hf₁.1.integrable_of_hasCompactSupport hf₁.2)
        (hf₂.1.integrable_of_hasCompactSupport hf₂.2),
        integral_add (hq₁.1.integrable_of_hasCompactSupport hq₁.2)
          (hq₂.1.integrable_of_hasCompactSupport hq₂.2), h₁, h₂, mul_add]
  intro Ψ
  change (χ (determinant (adjacentRankModelStarBasePoint (F := F.Carrier) r)) : ℂ) *
      determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData)
        (adjacentRankModelStarBasePoint (F := F.Carrier) r) (((r + 1 : ℕ) : ℂ) / 2) *
      (∫ h, adjacentRankModelStarSourceFunction ψ σ ℓ
        (normalizedAbsoluteValue F.canonicalTopologicalData) χ ((r : ℂ) / 2)
        (adjacentRankRho0 ψ ν hself σ ℓ
          (adjacentRankModelStarBasePoint (F := F.Carrier) r) Ψ) h
        ∂generalLinearHaar F.Carrier r) = _
  rw [hall, ← mul_assoc, adjacentRankModelStarBasePoint_prefactor, one_mul]
  apply integral_congr_ae
  filter_upwards [] with h
  simp only [adjacentRankTransformedIntegrand, adjacentRankRho0_one,
    adjacentRankModelStarTargetFunction]

include hσ in
/-- The fixed-character model-star identity at the ambient point `w * zeta`,
for every smooth representation and every original test tensor. -/
theorem adjacentRankModelStar_base :
    AdjacentRankBaseModelStarIdentity F ψ ν hself σ ℓ χ := by
  apply adjacentRankModelStarBase_of_pure_integrals F ψ ν hself σ hσ ℓ χ
  intro Φ W
  have hf := adjacentRankModelStarSourceFunction_regularity F ψ r σ hσ ℓ χ
    ((r : ℂ) / 2) (adjacentRankRho0 ψ ν hself σ ℓ
      (adjacentRankModelStarBasePoint (F := F.Carrier) r) (Φ ⊗ₜ W))
  have hq := adjacentRankModelStarTargetFunction_regularity F ψ r σ hσ ℓ χ
    ((r : ℂ) / 2) (adjacentRankFullFourier F ψ ν hself σ ℓ (Φ ⊗ₜ W))
  exact adjacentRank_integral_eq_of_reflected_right_averages F.Carrier r
    _ _ hf.1 hf.2 hq.1 hq.2 (χ (determinant (weylLong (r + 1) F.Carrier)))
    (adjacentRankModelStar_pure_right_averages F ψ ν hself σ ℓ χ Φ W)

end CanonicalTopology

end Langlands.RankinSelberg
