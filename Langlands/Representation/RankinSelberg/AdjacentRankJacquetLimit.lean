import Langlands.Representation.RankinSelberg.AdjacentRankJacquetIntegrability
import Langlands.Representation.RankinSelberg.AdjacentRankFullRankCutoff
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Pointwise model convergence for norm-bounded full-rank Schwartz approximations. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear AdjacentCompactMatrix
open Filter Topology Matrix
open scoped TensorProduct

universe uF uV

section Rank

variable {K : Type uF} [Field K] {r : ℕ}

/-- Every rectangle sampled by the translated double kernel has full row rank. -/
theorem adjacentRankFullRank_doubleKernel (h : GeneralLinear (r + 1) K)
    (x : Fin (r + 1) → K) (g : GeneralLinear (r + 2) K) :
    AdjacentRankFullRank (rectangularJoin h.val (h.val *ᵥ x) * g.val) := by
  rw [← AdjacentJacquet.rectangularJoin_mul_upperColumn,
    Matrix.mul_assoc, ← Units.val_mul]
  exact (adjacentRankFullRank_mul_iff _ _).mpr
    ((adjacentRankFullRank_join_zero_iff _).mpr h.isUnit)

end Rank

namespace AdjacentDoubleIntegral

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance jacquetLimitTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance jacquetLimitValuative : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance jacquetLimitLocalField : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance jacquetLimitT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance jacquetLimitNonarchRing : NonarchimedeanRing F.Carrier := by
  convert! ValuativeRel.nonarchimedeanRing F.Carrier
  exact Valuation.toTopologicalSpace_eq _
local instance jacquetLimitSecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance jacquetLimitMeasurable : MeasurableSpace F.Carrier := borel _
local instance jacquetLimitBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance jacquetLimitGLMeasurable (n : ℕ) : MeasurableSpace (GeneralLinear (n + 1) F.Carrier) := borel _
local instance jacquetLimitGLBorel (n : ℕ) : BorelSpace (GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance jacquetLimitGLLocallyCompact (n : ℕ) : LocallyCompactSpace (GeneralLinear (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearLocallyCompactSpace (n + 1)
local instance jacquetLimitGLSecondCountable (n : ℕ) : SecondCountableTopology (GeneralLinear (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology (n + 1)

local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData

variable (ν : AdditiveHaarMeasure F.Carrier) (ψ : UnitaryAdditiveCharacter F.Carrier)
  {r : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
  (hσ : IsOfWhittakerType r (standardCharacter ψ r) σ) (ℓ : glFunctionals ψ r σ)
  (χ₀ : Quasicharacter F.Carrier) (u : ℝ)
  (hu : realTwistThreshold F ψ σ hσ ℓ χ₀ < u)
  (W : (glCoefficientModel ψ r σ ℓ).toSubmodule)
  (Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F.Carrier))
  (Ψ : ℕ → SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F.Carrier))
  (hbound : ∀ n M, ‖Ψ n M‖ ≤ ‖Φ M‖)
  (hevent : ∀ M, AdjacentRankFullRank M → ∀ᶠ n in atTop, Ψ n M = Φ M)

include hσ hu hbound hevent in
/-- Dominated convergence on the genuine row-times-matrix measure, followed by
Fubini, for every ambient translate of the whole Schwartz test. -/
theorem tendsto_doubleIntegral (g : GeneralLinear (r + 2) F.Carrier) :
    Tendsto (fun n => ∫ x, ∫ h, integrand F ψ σ ℓ (realTwistedCharacter F χ₀ u)
      (rectangularTranslate g (Ψ n)) W x h
        ∂generalLinearHaar F.Carrier r ∂rowMeasure ν (r + 1)) atTop
      (𝓝 (∫ x, ∫ h, integrand F ψ σ ℓ (realTwistedCharacter F χ₀ u)
        (rectangularTranslate g Φ) W x h
          ∂generalLinearHaar F.Carrier r ∂rowMeasure ν (r + 1))) := by
  let K (Ξ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F.Carrier))
      (z : (Fin (r + 1) → F.Carrier) × GeneralLinear (r + 1) F.Carrier) :=
    integrand F ψ σ ℓ (realTwistedCharacter F χ₀ u) (rectangularTranslate g Ξ) W z.1 z.2
  have hi (Ξ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F.Carrier)) :
      Integrable (K Ξ) ((rowMeasure ν (r + 1)).prod (generalLinearHaar F.Carrier r)) :=
    integrable_realTwist F ν ψ σ hσ ℓ χ₀ u hu W (rectangularTranslate g Ξ)
  have hd := tendsto_integral_of_dominated_convergence (f := K Φ) (fun z => ‖K Φ z‖)
    (fun n => (hi (Ψ n)).aestronglyMeasurable) (hi Φ).norm
    (fun n => Filter.Eventually.of_forall fun z => ?_) (Filter.Eventually.of_forall fun z => ?_)
  · simpa only [integral_prod _ (hi _)] using hd
  · dsimp only [K, integrand, rectangularTranslate_apply]
    simp only [norm_mul]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hbound n _) (norm_nonneg _)) (norm_nonneg _))
        (norm_nonneg _)) (norm_nonneg _)
  · apply tendsto_const_nhds.congr'
    filter_upwards [hevent _ (adjacentRankFullRank_doubleKernel z.2 z.1 g)] with n hn
    dsimp only [K, integrand, rectangularTranslate_apply]
    rw [hn]

include hσ hu hbound hevent in
/-- The actual model integrals of the partial Fourier transforms converge
pointwise, with the original threshold and supplied Haar normalization. -/
theorem tendsto_modelIntegral (hself : IsSelfDual ψ ν)
    (g : GeneralLinear (r + 2) F.Carrier) :
    Tendsto (fun n => adjacentRankModelIntegral ψ ν hself σ ℓ abv
      (realTwistedCharacter F χ₀ u) (generalLinearHaar F.Carrier r)
      ((partialFourierEquiv ψ ν (r + 1) hself (Ψ n)) ⊗ₜ[ℂ] W) g) atTop
      (𝓝 (adjacentRankModelIntegral ψ ν hself σ ℓ abv
        (realTwistedCharacter F χ₀ u) (generalLinearHaar F.Carrier r)
        ((partialFourierEquiv ψ ν (r + 1) hself Φ) ⊗ₜ[ℂ] W) g)) := by
  simp_rw [← double_integral_eq_modelIntegral F ν ψ hself σ hσ ℓ χ₀ u hu W]
  exact (tendsto_doubleIntegral F ν ψ σ hσ ℓ χ₀ u hu W Φ Ψ hbound hevent g).const_mul _

end AdjacentDoubleIntegral

namespace AdjacentJacquet

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance jacquetCoefficientTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance jacquetCoefficientMeasurable : MeasurableSpace F.Carrier := borel _
local instance jacquetCoefficientBorel : BorelSpace F.Carrier := ⟨rfl⟩

variable (ψ : UnitaryAdditiveCharacter F.Carrier) {r : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
  (ℓ : glFunctionals ψ r σ) (ν : AdditiveHaarMeasure F.Carrier)
  (hσ : IsOfWhittakerType r (standardCharacter ψ r) σ)
  (χ₀ : Quasicharacter F.Carrier) (u : ℝ)
  (hu : realTwistThreshold F ψ σ hσ ℓ χ₀ < u)

/-- All coefficients of the one identity Jacquet integral as a scalar linear map. -/
def realTwistCoefficientMap :
    (inducedRepresentation F σ (realTwistedCharacter F χ₀ u)).asModule →ₗ[ℂ]
      (GeneralLinear (r + 2) F.Carrier → ℂ) where
  toFun f g := realTwistIntegralLinear F ψ σ ℓ ν hσ χ₀ u hu g f
  map_add' f f' := by
    funext g
    exact (realTwistIntegralLinear F ψ σ ℓ ν hσ χ₀ u hu g).map_add f f'
  map_smul' c f := by
    funext g
    exact (realTwistIntegralLinear F ψ σ ℓ ν hσ χ₀ u hu g).map_smul c f

@[simp] theorem realTwistCoefficientMap_apply
    (f : (inducedRepresentation F σ (realTwistedCharacter F χ₀ u)).asModule)
    (g : GeneralLinear (r + 2) F.Carrier) :
    realTwistCoefficientMap F ψ σ ℓ ν hσ χ₀ u hu f g =
      integral F ψ σ ℓ (realTwistedCharacter F χ₀ u) ν f g :=
  rfl

/-- This linear map consists of coefficients of one fixed identity integral. -/
theorem realTwistCoefficientMap_coefficient
    (f : (inducedRepresentation F σ (realTwistedCharacter F χ₀ u)).asModule)
    (g : GeneralLinear (r + 2) F.Carrier) :
    realTwistCoefficientMap F ψ σ ℓ ν hσ χ₀ u hu f g =
      realTwistIntegralLinear F ψ σ ℓ ν hσ χ₀ u hu 1
        (inducedRepresentation F σ (realTwistedCharacter F χ₀ u) g f) :=
  (realTwistIntegralLinear_coefficient F ψ σ ℓ ν hσ χ₀ u hu f g).symm

end AdjacentJacquet

end Langlands.RankinSelberg
