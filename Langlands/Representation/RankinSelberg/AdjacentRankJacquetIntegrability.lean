import Langlands.Representation.RankinSelberg.AdjacentRankSectionSurjectivity
import Langlands.Representation.RankinSelberg.AdjacentRankJacquetLinear
import Langlands.Representation.RankinSelberg.AdjacentRankModelMap

/-! All-section convergence and coefficient containment for the actual induction. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.RankinSelberg.AdjacentJacquet

open MeasureTheory HarmonicAnalysis Whittaker AdjacentCompactMatrix
open scoped TensorProduct

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance : TotallyDisconnectedSpace F.Carrier := by
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance : MeasurableSpace F.Carrier := borel _
local instance : BorelSpace F.Carrier := ⟨rfl⟩
local instance (n : ℕ) : MeasurableSpace (GeneralLinear (n + 1) F.Carrier) := borel _
local instance (n : ℕ) : BorelSpace (GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩

variable (ψ : UnitaryAdditiveCharacter F.Carrier) {r : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
  (ℓ : glFunctionals ψ r σ) (ν : AdditiveHaarMeasure F.Carrier)
  (hσ : IsOfWhittakerType r (standardCharacter ψ r) σ)
  (χ₀ : Quasicharacter F.Carrier) (u : ℝ)
  (hu : AdjacentCompactMatrix.realTwistThreshold F ψ σ hσ ℓ χ₀ < u)

include hσ hu in
/-- The same representation-uniform real-twist threshold makes the literal
Jacquet kernel integrable for every actual induced section and every translate. -/
theorem integrable_realTwist
    (f : (inducedRepresentation F σ (realTwistedCharacter F χ₀ u)).asModule)
    (g : GeneralLinear (r + 2) F.Carrier) :
    Integrable (integrand F ψ σ ℓ (realTwistedCharacter F χ₀ u) f g)
      (rowMeasure ν (r + 1)) := by
  obtain ⟨t, rfl⟩ := Padic.adjacentRankNormalizedSectionTensor_surjective
    F σ (realTwistedCharacter F χ₀ u) hσ.1.1 f
  induction t using TensorProduct.inductionOn with
  | tmul Φ v =>
    exact integrable_normalizedSection_realTwist F ψ σ ℓ ν hσ χ₀ u hu Φ v g
  | add a b ha hb =>
    have hadd : integrand F ψ σ ℓ (realTwistedCharacter F χ₀ u)
        (Padic.adjacentRankNormalizedSectionTensor F σ
          (realTwistedCharacter F χ₀ u) hσ.1.1 (a + b)) g =
        integrand F ψ σ ℓ (realTwistedCharacter F χ₀ u)
          (Padic.adjacentRankNormalizedSectionTensor F σ
            (realTwistedCharacter F χ₀ u) hσ.1.1 a) g +
        integrand F ψ σ ℓ (realTwistedCharacter F χ₀ u)
          (Padic.adjacentRankNormalizedSectionTensor F σ
            (realTwistedCharacter F χ₀ u) hσ.1.1 b) g := by
      rw [map_add]
      exact (integrandLinear F ψ σ ℓ (realTwistedCharacter F χ₀ u) g).map_add
        _ _ |>.trans (by rfl)
    rw [hadd]
    exact ha.add hb

/-- The literal integral at any ambient element, with convergence discharged
on the exact original-carrier normalized opposite induction. -/
def realTwistIntegralLinear (g : GeneralLinear (r + 2) F.Carrier) :
    (inducedRepresentation F σ (realTwistedCharacter F χ₀ u)).asModule →ₗ[ℂ] ℂ :=
  integralLinear F ψ σ ℓ (realTwistedCharacter F χ₀ u) ν
    (integrable_realTwist F ψ σ ℓ ν hσ χ₀ u hu) g

@[simp] theorem realTwistIntegralLinear_apply
    (g : GeneralLinear (r + 2) F.Carrier)
    (f : (inducedRepresentation F σ (realTwistedCharacter F χ₀ u)).asModule) :
    realTwistIntegralLinear F ψ σ ℓ ν hσ χ₀ u hu g f =
      integral F ψ σ ℓ (realTwistedCharacter F χ₀ u) ν f g := rfl

/-- Every coefficient of the identity integral is the literal integral at g. -/
theorem realTwistIntegralLinear_coefficient
    (f : (inducedRepresentation F σ (realTwistedCharacter F χ₀ u)).asModule)
    (g : GeneralLinear (r + 2) F.Carrier) :
    realTwistIntegralLinear F ψ σ ℓ ν hσ χ₀ u hu 1
      (inducedRepresentation F σ (realTwistedCharacter F χ₀ u) g f) =
      integral F ψ σ ℓ (realTwistedCharacter F χ₀ u) ν f g :=
  integralLinear_coefficient F ψ σ ℓ (realTwistedCharacter F χ₀ u) ν
    (integrable_realTwist F ψ σ ℓ ν hσ χ₀ u hu) f g

/-- The compact-test tensor maps into the whole model test space by the
specified partial Fourier transform and the original coefficient quotient. -/
def compactTestModelTensor (hself : IsSelfDual ψ ν) :
    TensorProduct ℂ (adjacentRankCompactTests (r + 1) F.Carrier) V →ₗ[ℂ]
      adjacentRankTestSpace ψ σ ℓ :=
  TensorProduct.map
    ((partialFourierEquiv ψ ν (r + 1) hself).toLinearMap.comp
      (adjacentRankCompactTests (r + 1) F.Carrier).subtype)
    (modelMap σ ℓ).toLinearMap

@[simp] theorem compactTestModelTensor_tmul (hself : IsSelfDual ψ ν)
    (Φ : adjacentRankCompactTests (r + 1) F.Carrier) (v : V) :
    compactTestModelTensor F ψ σ ℓ ν hself (Φ ⊗ₜ[ℂ] v) =
      (partialFourierEquiv ψ ν (r + 1) hself Φ.val) ⊗ₜ[ℂ] (modelMap σ ℓ v) := rfl

include hu in
/-- Exact comparison on the entire compact-test/original-vector tensor product. -/
theorem integral_normalizedSectionTensor_eq_modelIntegral (hself : IsSelfDual ψ ν)
    (t : TensorProduct ℂ (adjacentRankCompactTests (r + 1) F.Carrier) V) :
    (fun g => integral F ψ σ ℓ (realTwistedCharacter F χ₀ u) ν
      (Padic.adjacentRankNormalizedSectionTensor F σ
        (realTwistedCharacter F χ₀ u) hσ.1.1 t) g) =
    Padic.adjacentRankModelMap F ψ ν hself σ ℓ
      (realTwistedCharacter F χ₀ u) hσ.1.1
      (compactTestModelTensor F ψ σ ℓ ν hself t) := by
  induction t using TensorProduct.inductionOn with
  | tmul Φ v =>
    funext g
    exact integral_normalizedSection_eq_modelIntegral F ψ σ ℓ ν hself
      hσ χ₀ u hu Φ v g
  | add a b ha hb =>
    funext g
    change realTwistIntegralLinear F ψ σ ℓ ν hσ χ₀ u hu g
      (Padic.adjacentRankNormalizedSectionTensor F σ
        (realTwistedCharacter F χ₀ u) hσ.1.1 (a + b)) = _
    simp only [map_add, Pi.add_apply]
    exact congrFun ha g ▸ congrFun hb g ▸ rfl

/-- Every coefficient of the common integral belongs to the whole model image.
The reverse inclusion, for all Schwartz tests, is a separate obligation. -/
theorem range_realTwistIntegralLinear_coefficients_subset (hself : IsSelfDual ψ ν) :
    Set.range (fun f => fun g => realTwistIntegralLinear F ψ σ ℓ ν hσ χ₀ u hu 1
      (inducedRepresentation F σ (realTwistedCharacter F χ₀ u) g f)) ⊆
    Set.range (Padic.adjacentRankModelMap F ψ ν hself σ ℓ
      (realTwistedCharacter F χ₀ u) hσ.1.1) := by
  rintro _ ⟨f, rfl⟩
  obtain ⟨t, rfl⟩ := Padic.adjacentRankNormalizedSectionTensor_surjective
    F σ (realTwistedCharacter F χ₀ u) hσ.1.1 f
  refine ⟨compactTestModelTensor F ψ σ ℓ ν hself t, ?_⟩
  rw [← integral_normalizedSectionTensor_eq_modelIntegral F ψ σ ℓ ν hσ χ₀ u hu hself t]
  funext g
  exact (realTwistIntegralLinear_coefficient F ψ σ ℓ ν hσ χ₀ u hu _ g).symm

end Langlands.RankinSelberg.AdjacentJacquet
