import Langlands.Representation.RankinSelberg.AdjacentRankModelStarIntegrability

/-! Continuous compactly supported scalar evaluations of whole test tensors. -/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker TensorProduct GeneralLinear

universe uF uV

section Evaluation

variable {F : Type uF} [Field F] [TopologicalSpace F]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ψ : UnitaryAdditiveCharacter F) {r : ℕ}
  (σ : Representation ℂ (GeneralLinear (r + 1) F) V) (ℓ : glFunctionals ψ r σ)
  (abv : AbsoluteValue F ℝ) (χ : Quasicharacter F) (s : ℂ)

/-- Weighted scalar evaluation at the original coefficient argument. -/
def adjacentRankModelStarSourceFunction (Ψ : adjacentRankTestSpace ψ σ ℓ)
    (h : GeneralLinear (r + 1) F) : ℂ :=
  adjacentRankTestEvaluation ψ σ ℓ Ψ (adjacentRankKernelMatrix h) h⁻¹ *
    (χ (determinant h) : ℂ) * determinantWeight abv h s

/-- Weighted scalar evaluation at the displayed transformed coefficient
argument, with the inverse quasicharacter. -/
def adjacentRankModelStarTargetFunction (Ψ : adjacentRankTestSpace ψ σ ℓ)
    (h : GeneralLinear (r + 1) F) : ℂ :=
  adjacentRankTestEvaluation ψ σ ℓ Ψ (adjacentRankKernelMatrix h)
      (weylLong (r + 1) F * inverseTranspose (r + 1) F h⁻¹) *
    (χ⁻¹ (determinant h) : ℂ) * determinantWeight abv h s

theorem adjacentRankModelStarSourceFunction_add (Ψ₁ Ψ₂ : adjacentRankTestSpace ψ σ ℓ) :
    adjacentRankModelStarSourceFunction ψ σ ℓ abv χ s (Ψ₁ + Ψ₂) =
      adjacentRankModelStarSourceFunction ψ σ ℓ abv χ s Ψ₁ +
        adjacentRankModelStarSourceFunction ψ σ ℓ abv χ s Ψ₂ := by
  funext h
  simp only [adjacentRankModelStarSourceFunction, adjacentRankTestEvaluation_add,
    add_mul, Pi.add_apply]

theorem adjacentRankModelStarTargetFunction_add (Ψ₁ Ψ₂ : adjacentRankTestSpace ψ σ ℓ) :
    adjacentRankModelStarTargetFunction ψ σ ℓ abv χ s (Ψ₁ + Ψ₂) =
      adjacentRankModelStarTargetFunction ψ σ ℓ abv χ s Ψ₁ +
        adjacentRankModelStarTargetFunction ψ σ ℓ abv χ s Ψ₂ := by
  funext h
  simp only [adjacentRankModelStarTargetFunction, adjacentRankTestEvaluation_add,
    add_mul, Pi.add_apply]

end Evaluation

section CanonicalTopology

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance modelStarRegularityTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance modelStarRegularityValuative : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance modelStarRegularityLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance modelStarRegularityT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ψ : UnitaryAdditiveCharacter F.Carrier) (r : ℕ)
  (σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
  (hσ : IsSmooth σ) (ℓ : glFunctionals ψ r σ) (χ : Quasicharacter F.Carrier)
  (s : ℂ)

include hσ

/-- Every original weighted tensor evaluation is continuous with compact
support. No topology on the coefficient module is used. -/
theorem adjacentRankModelStarSourceFunction_regularity
    (Ψ : adjacentRankTestSpace ψ σ ℓ) :
    Continuous (adjacentRankModelStarSourceFunction ψ σ ℓ
      (normalizedAbsoluteValue F.canonicalTopologicalData) χ s Ψ) ∧
    HasCompactSupport (adjacentRankModelStarSourceFunction ψ σ ℓ
      (normalizedAbsoluteValue F.canonicalTopologicalData) χ s Ψ) := by
  induction Ψ using adjacentRankTestSpace_induction ψ σ ℓ with
  | tmul Φ W =>
    constructor
    · have hχ : Continuous (fun h : GeneralLinear (r + 1) F.Carrier =>
          (χ (determinant h) : ℂ)) :=
        Units.continuous_val.comp (χ.continuous.comp determinantContinuous.continuous)
      exact ((((SchwartzBruhat.continuous Φ).comp
        (continuous_adjacentRankKernelMatrix F r)).mul
          ((glModelFunction_continuous ψ r σ hσ ℓ W).comp continuous_inv)).mul hχ).mul
            (continuous_adjacentRank_determinantWeight F _ _)
    · exact ((adjacentRankPure_hasCompactSupport F ψ r σ hσ ℓ Φ W).mul_right).mul_right
  | add Ψ₁ Ψ₂ h₁ h₂ =>
    rw [adjacentRankModelStarSourceFunction_add]
    exact ⟨h₁.1.add h₂.1, h₁.2.add h₂.2⟩

/-- Every weighted tensor evaluation at the transformed coefficient argument
is continuous with compact support, in the original tensor space. -/
theorem adjacentRankModelStarTargetFunction_regularity
    (Ψ : adjacentRankTestSpace ψ σ ℓ) :
    Continuous (adjacentRankModelStarTargetFunction ψ σ ℓ
      (normalizedAbsoluteValue F.canonicalTopologicalData) χ s Ψ) ∧
    HasCompactSupport (adjacentRankModelStarTargetFunction ψ σ ℓ
      (normalizedAbsoluteValue F.canonicalTopologicalData) χ s Ψ) := by
  induction Ψ using adjacentRankTestSpace_induction ψ σ ℓ with
  | tmul Φ W =>
    constructor
    · have hχ : Continuous (fun h : GeneralLinear (r + 1) F.Carrier =>
          (χ⁻¹ (determinant h) : ℂ)) :=
        Units.continuous_val.comp ((χ⁻¹).continuous.comp determinantContinuous.continuous)
      have harg : Continuous (fun h : GeneralLinear (r + 1) F.Carrier =>
          weylLong (r + 1) F.Carrier * inverseTranspose (r + 1) F.Carrier h⁻¹) :=
        continuous_const.mul ((continuous_inverseTranspose _ _).comp continuous_inv)
      exact ((((SchwartzBruhat.continuous Φ).comp
        (continuous_adjacentRankKernelMatrix F r)).mul
          ((glModelFunction_continuous ψ r σ hσ ℓ W).comp harg)).mul hχ).mul
            (continuous_adjacentRank_determinantWeight F _ _)
    · exact ((adjacentRankTransformedPure_hasCompactSupport F ψ r σ hσ ℓ Φ W).mul_right).mul_right
  | add Ψ₁ Ψ₂ h₁ h₂ =>
    rw [adjacentRankModelStarTargetFunction_add]
    exact ⟨h₁.1.add h₂.1, h₁.2.add h₂.2⟩

end CanonicalTopology

end Langlands.RankinSelberg
