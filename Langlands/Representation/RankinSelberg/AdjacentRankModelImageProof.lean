import Langlands.Representation.RankinSelberg.AdjacentRankModelImageStatement
import Langlands.Representation.RankinSelberg.AdjacentRankAdmissibility
import Langlands.Representation.RankinSelberg.AdjacentRankJacquetLimit
import Langlands.Representation.RankinSelberg.AdjacentRankInvariantApproximation
import Langlands.Representation.RankinSelberg.AdjacentRankJacquetNonzero

/-! Whole-function image equality for the actual normalized adjacent induction. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.RankinSelberg.AdjacentJacquet

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear AdjacentCompactMatrix
open Filter Topology
open scoped TensorProduct

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance modelImageTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance modelImageValuative : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance modelImageLocalField : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance modelImageT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance modelImageNonarchRing : NonarchimedeanRing F.Carrier := by
  convert! ValuativeRel.nonarchimedeanRing F.Carrier
  exact Valuation.toTopologicalSpace_eq _
local instance modelImageMeasurable : MeasurableSpace F.Carrier := borel _
local instance modelImageBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance modelImageGLMeasurable (n : ℕ) : MeasurableSpace (GeneralLinear (n + 1) F.Carrier) := borel _
local instance modelImageGLBorel (n : ℕ) : BorelSpace (GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩

variable (ψ : UnitaryAdditiveCharacter F.Carrier) {r : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
  (ℓ : glFunctionals ψ r σ) (ν : AdditiveHaarMeasure F.Carrier)
  (hσ : IsOfWhittakerType r (standardCharacter ψ r) σ)
  (χ₀ : Quasicharacter F.Carrier) (u : ℝ)
  (hu : realTwistThreshold F ψ σ hσ ℓ χ₀ < u)

local notation "χᵤ" => realTwistedCharacter F χ₀ u
local notation "ρᵤ" => inducedRepresentation F σ χᵤ

/-- The limit of cutoff-section coefficients belongs to the coefficients of the
same identity integral, using admissibility of the actual original-carrier induction. -/
theorem modelIntegral_mem_range_of_fixed_approximation (hself : IsSelfDual ψ ν)
    (Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F.Carrier))
    (v : V) (J : OpenSubgroup (GeneralLinear (r + 2) F.Carrier))
    (Ψ : ℕ → adjacentRankCompactTests (r + 1) F.Carrier)
    (hfixed : ∀ n, Padic.adjacentRankNormalizedSection F σ χᵤ hσ.1.1 (Ψ n) v ∈
      fixedVectors ρᵤ J.toSubgroup)
    (hbound : ∀ n M, ‖(Ψ n).val M‖ ≤ ‖Φ M‖)
    (hevent : ∀ M, AdjacentRankFullRank M → ∀ᶠ n in atTop, (Ψ n).val M = Φ M) :
    Padic.adjacentRankModelMap F ψ ν hself σ ℓ χᵤ hσ.1.1
      ((partialFourierEquiv ψ ν (r + 1) hself Φ) ⊗ₜ[ℂ] modelMap σ ℓ v) ∈
      Set.range (realTwistCoefficientMap F ψ σ ℓ ν hσ χ₀ u hu) := by
  let L := realTwistIntegralLinear F ψ σ ℓ ν hσ χ₀ u hu 1
  let f (n : ℕ) : fixedVectors ρᵤ J.toSubgroup :=
    ⟨Padic.adjacentRankNormalizedSection F σ χᵤ hσ.1.1 (Ψ n) v, hfixed n⟩
  have hlim (g : GeneralLinear (r + 2) F.Carrier) :
      Tendsto (fun n => L (ρᵤ g (f n).val)) atTop
        (𝓝 (Padic.adjacentRankModelMap F ψ ν hself σ ℓ χᵤ hσ.1.1
          ((partialFourierEquiv ψ ν (r + 1) hself Φ) ⊗ₜ[ℂ] modelMap σ ℓ v) g)) := by
    have hd := AdjacentDoubleIntegral.tendsto_modelIntegral F ν ψ σ hσ ℓ χ₀ u hu
      (modelMap σ ℓ v) Φ (fun n => (Ψ n).val) hbound hevent hself g
    have heq (n : ℕ) : L (ρᵤ g (f n).val) =
        Padic.adjacentRankModelMap F ψ ν hself σ ℓ χᵤ hσ.1.1
          ((partialFourierEquiv ψ ν (r + 1) hself (Ψ n).val) ⊗ₜ[ℂ] modelMap σ ℓ v) g := by
      dsimp only [L, f]
      rw [realTwistIntegralLinear_coefficient]
      exact integral_normalizedSection_eq_modelIntegral F ψ σ ℓ ν hself hσ χ₀ u hu (Ψ n) v g
    simpa only [heq, Padic.adjacentRankModelMap_apply, Padic.adjacentRankModelIntegral] using hd
  obtain ⟨f₀, hf₀⟩ := mem_range_fixedCoefficientMap_of_tendsto ρᵤ L J
    (Padic.adjacentRankNormalizedInduced_isAdmissible F σ χᵤ hσ.1) f _ hlim
  refine ⟨f₀.val, ?_⟩
  funext g
  rw [realTwistCoefficientMap_coefficient]
  exact congrFun hf₀ g

/-- Every whole-function model integral of a pure tensor is a coefficient of the
same identity integral on the actual original-carrier induction. -/
theorem modelIntegral_tmul_mem_range (hself : IsSelfDual ψ ν)
    (Φ : SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) F.Carrier))
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule) :
    Padic.adjacentRankModelMap F ψ ν hself σ ℓ χᵤ hσ.1.1 (Φ ⊗ₜ[ℂ] W) ∈
      Set.range (realTwistCoefficientMap F ψ σ ℓ ν hσ χ₀ u hu) := by
  obtain ⟨v, rfl⟩ := modelMap_surjective σ ℓ W
  let Φ₀ := (partialFourierEquiv ψ ν (r + 1) hself).symm Φ
  let A := Padic.adjacentRankInvariantApproximation F σ χᵤ hσ.1.1 Φ₀
  have h := modelIntegral_mem_range_of_fixed_approximation F ψ σ ℓ ν hσ χ₀ u hu
    hself Φ₀ v A.level A.tests (fun n => A.fixed n v) A.norm_le A.eventually_eq
  simpa only [Φ₀, LinearEquiv.apply_symm_apply] using h

/-- All finite algebraic test tensors give coefficients of the common integral. -/
theorem range_modelIntegral_subset (hself : IsSelfDual ψ ν) :
    Set.range (Padic.adjacentRankModelMap F ψ ν hself σ ℓ χᵤ hσ.1.1) ⊆
      Set.range (realTwistCoefficientMap F ψ σ ℓ ν hσ χ₀ u hu) := by
  rintro _ ⟨t, rfl⟩
  change Padic.adjacentRankModelMap F ψ ν hself σ ℓ χᵤ hσ.1.1 t ∈
    LinearMap.range (realTwistCoefficientMap F ψ σ ℓ ν hσ χ₀ u hu)
  induction t using TensorProduct.inductionOn with
  | tmul Φ W =>
    exact modelIntegral_tmul_mem_range F ψ σ ℓ ν hσ χ₀ u hu hself Φ W
  | add a b ha hb =>
    rw [map_add]
    exact Submodule.add_mem _ ha hb

/-- Whole-function range equality at the original uniform twist threshold. -/
theorem range_modelIntegral_eq (hself : IsSelfDual ψ ν) :
    Set.range (Padic.adjacentRankModelMap F ψ ν hself σ ℓ χᵤ hσ.1.1) =
      Set.range (realTwistCoefficientMap F ψ σ ℓ ν hσ χ₀ u hu) := by
  apply Set.Subset.antisymm
  · exact range_modelIntegral_subset F ψ σ ℓ ν hσ χ₀ u hu hself
  · have heq : (fun f => fun g => realTwistIntegralLinear F ψ σ ℓ ν hσ χ₀ u hu 1
        (ρᵤ g f)) = realTwistCoefficientMap F ψ σ ℓ ν hσ χ₀ u hu := by
      funext f g
      exact (realTwistCoefficientMap_coefficient F ψ σ ℓ ν hσ χ₀ u hu f g).symm
    rw [← heq]
    exact range_realTwistIntegralLinear_coefficients_subset F ψ σ ℓ ν hσ χ₀ u hu hself

end Langlands.RankinSelberg.AdjacentJacquet

namespace Langlands.RankinSelberg

open HarmonicAnalysis Whittaker AdjacentCompactMatrix AdjacentJacquet

/-- The full JPSS adjacent-rank model image is the coefficient image of one
nonzero standard Whittaker functional on the actual normalized lower induction. -/
theorem adjacentRankModelImage.{uF,uV} : AdjacentRankModelImageStatement.{uF,uV} := by
  intro p _ F
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let : MeasurableSpace F.Carrier := borel _
  have : BorelSpace F.Carrier := ⟨rfl⟩
  have : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
  have : TotallyDisconnectedSpace F.Carrier := by
    let : NonarchimedeanRing F.Carrier := by
      convert! ValuativeRel.nonarchimedeanRing F.Carrier
      exact Valuation.toTopologicalSpace_eq _
    infer_instance
  intro ψ ν hself r V _ _ σ hσ ℓ hℓ χ₀
  refine ⟨realTwistThreshold F ψ σ hσ ℓ χ₀, ?_⟩
  intro u hu
  let χᵤ := realTwistedCharacter F χ₀ u
  let hI := integrable_realTwist F ψ σ ℓ ν hσ χ₀ u hu
  refine ⟨functional F ψ σ ℓ χᵤ ν hI,
    functional_ne_zero F ψ σ ℓ χᵤ ν hσ.1.1 hℓ hI, ?_⟩
  change Set.range (Padic.adjacentRankModelMap F ψ ν hself σ ℓ χᵤ hσ.1.1) = _
  rw [range_modelIntegral_eq F ψ σ ℓ ν hσ χ₀ u hu hself]
  congr 1
  funext f g
  exact (functional_coefficient F ψ σ ℓ χᵤ ν hI f g).symm

end Langlands.RankinSelberg
