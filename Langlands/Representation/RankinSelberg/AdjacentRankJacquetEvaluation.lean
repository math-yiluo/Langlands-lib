import Langlands.Representation.RankinSelberg.AdjacentRankNormalizedSection
import Langlands.Representation.RankinSelberg.AdjacentRankDoubleIntegral
import Langlands.Representation.Shahidi.Characters

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory Matrix
open scoped TensorProduct

namespace Langlands.RankinSelberg.AdjacentJacquet

open HarmonicAnalysis Whittaker GeneralLinear AdjacentCompactMatrix

universe uF uV

section Column

variable {K : Type uF} [Field K] {r : ℕ}

/-- The actual upper column matrix `[I,x;0,1]` in the host's ambient rank. -/
def upperColumn (x : Fin (r + 1) → K) : GeneralLinear (r + 2) K :=
  Shahidi.upper (r + 1) 1 K (fun i _ => x i)

@[simp] theorem upperColumn_castSucc_castSucc (x : Fin (r + 1) → K)
    (i j : Fin (r + 1)) :
    upperColumn x i.castSucc j.castSucc = if i = j then 1 else 0 :=
  Shahidi.upper_first_first (r + 1) 1 K _ i j

@[simp] theorem upperColumn_castSucc_last (x : Fin (r + 1) → K)
    (i : Fin (r + 1)) : upperColumn x i.castSucc (Fin.last (r + 1)) = x i :=
  Shahidi.upper_first_second (r + 1) 1 K _ i 0

@[simp] theorem upperColumn_last_castSucc (x : Fin (r + 1) → K)
    (j : Fin (r + 1)) : upperColumn x (Fin.last (r + 1)) j.castSucc = 0 :=
  Shahidi.upper_second_first (r + 1) 1 K _ 0 j

@[simp] theorem upperColumn_last_last (x : Fin (r + 1) → K) :
    upperColumn x (Fin.last (r + 1)) (Fin.last (r + 1)) = 1 := by
  exact Shahidi.upper_second_second (r + 1) 1 K _ 0 0

@[simp] theorem determinant_upperColumn (x : Fin (r + 1) → K) :
    determinant (upperColumn x) = 1 := by
  apply Units.ext
  change (Matrix.reindex finSumFinEquiv finSumFinEquiv
    (Matrix.fromBlocks 1 (Matrix.of (fun i (_ : Fin 1) => x i)) 0 1)).det = 1
  rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_one, Matrix.det_one, mul_one]

/-- The literal rectangular identity behind the Jacquet double integral. -/
theorem rectangularJoin_mul_upperColumn (A : Matrix (Fin (r + 1)) (Fin (r + 1)) K)
    (x : Fin (r + 1) → K) :
    rectangularJoin A 0 * (upperColumn x).val = rectangularJoin A (A *ᵥ x) := by
  ext i j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · simp [Matrix.mul_apply, Fin.sum_univ_castSucc, Matrix.mulVec, dotProduct]
  · simp [Matrix.mul_apply, Fin.sum_univ_castSucc]

end Column

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance jacquetEvaluationTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance jacquetEvaluationValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance jacquetEvaluationLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance jacquetEvaluationT2 : T2Space F.Carrier :=
  F.canonicalTopologicalData.fieldT2
local instance jacquetEvaluationNonarchRing : NonarchimedeanRing F.Carrier := by
  convert! ValuativeRel.nonarchimedeanRing F.Carrier
  exact Valuation.toTopologicalSpace_eq _
local instance jacquetEvaluationMeasurable : MeasurableSpace F.Carrier := borel _
local instance jacquetEvaluationBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance jacquetEvaluationGLMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear (n + 1) F.Carrier) := borel _
local instance jacquetEvaluationGLBorel (n : ℕ) :
    BorelSpace (GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance jacquetEvaluationGLLocallyCompact (n : ℕ) :
    LocallyCompactSpace (GeneralLinear (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearLocallyCompactSpace (n + 1)
local instance jacquetEvaluationGLSecondCountable (n : ℕ) :
    SecondCountableTopology (GeneralLinear (n + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology (n + 1)

local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData

/-- The smooth determinant character agrees with the exact scalar integral weight. -/
theorem determinantWeight_eq (χ : Quasicharacter F.Carrier) (n : ℕ)
    (s : ℂ) (g : GeneralLinear n F.Carrier) :
    ((adjacentRankDeterminantWeight F.canonicalTopologicalData χ n s).toMonoidHom g : ℂ) =
      (χ (determinant g) : ℂ) * determinantWeight abv g s := by
  rw [adjacentRankDeterminantWeight_apply, Units.val_mul,
    F.canonicalTopologicalData.determinantComplexPower_apply]
  rfl

variable (ψ : UnitaryAdditiveCharacter F.Carrier) {r : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
  (ℓ : glFunctionals ψ r σ) (χ : Quasicharacter F.Carrier)

/-- Scalar evaluation of an actual normalized section through the original module. -/
def sectionCoefficient
    (f : (F.canonicalNormalizedOppositeParabolicInduced (adjacentRankLowerShape r)
      ((adjacentRankLowerShape r).blockTensor
        (Shahidi.pairFamily σ (rankOneExtensionCharacter.{uF, uV} F χ)))).asModule)
    (g : GeneralLinear (r + 2) F.Carrier) : ℂ :=
  ℓ.val (adjacentRankLowerTensorCoordinates V
    (Induction.eval ((adjacentRankLowerShape r).oppositeParabolic F.Carrier)
      (Padic.adjacentRankLowerTensorRepresentation F σ χ) f g))

/-- The literal scalar Jacquet kernel, with the inverse last-coordinate phase. -/
def integrand
    (f : (F.canonicalNormalizedOppositeParabolicInduced (adjacentRankLowerShape r)
      ((adjacentRankLowerShape r).blockTensor
        (Shahidi.pairFamily σ (rankOneExtensionCharacter.{uF, uV} F χ)))).asModule)
    (g : GeneralLinear (r + 2) F.Carrier) (x : Fin (r + 1) → F.Carrier) : ℂ :=
  sectionCoefficient F ψ σ ℓ χ f (upperColumn x * g) *
    ψ.complex (-x (Fin.last r))

/-- Pure normalized sections retain their original-carrier algebraic average
after scalar evaluation. -/
theorem sectionCoefficient_normalizedSection (hσ : IsSmooth σ)
    (Φ : adjacentRankCompactTests (r + 1) F.Carrier) (v : V)
    (g : GeneralLinear (r + 2) F.Carrier) :
    sectionCoefficient F ψ σ ℓ χ (Padic.adjacentRankNormalizedSection F σ χ hσ Φ v) g =
      ((adjacentRankDeterminantWeight F.canonicalTopologicalData χ
        (r + 2) (((r + 1 : ℕ) : ℂ) / 2)).toMonoidHom g : ℂ) *
      (∫ h, Φ.val (rectangularJoin h.val 0 * g.val) *
        ((adjacentRankDeterminantWeight F.canonicalTopologicalData χ
          (r + 1) (((r + 2 : ℕ) : ℂ) / 2)).toMonoidHom h : ℂ) *
        ℓ.val (σ h⁻¹ v) ∂generalLinearHaar F.Carrier r) := by
  unfold sectionCoefficient
  rw [Padic.adjacentRankNormalizedSection_eval,
    adjacentRankLowerTensorCoordinates_pairTensor, one_smul, map_smul,
    smul_eq_mul, adjacentRankCompactAverage_dual]

/-- The actual pure-section Jacquet kernel is the translated literal inner
integral, with precisely the ambient normalized determinant weight. -/
theorem integrand_normalizedSection (hσ : IsSmooth σ)
    (Φ : adjacentRankCompactTests (r + 1) F.Carrier) (v : V)
    (g : GeneralLinear (r + 2) F.Carrier) (x : Fin (r + 1) → F.Carrier) :
    integrand F ψ σ ℓ χ (Padic.adjacentRankNormalizedSection F σ χ hσ Φ v) g x =
      ((adjacentRankDeterminantWeight F.canonicalTopologicalData χ
        (r + 2) (((r + 1 : ℕ) : ℂ) / 2)).toMonoidHom g : ℂ) *
      ∫ h, AdjacentDoubleIntegral.integrand F ψ σ ℓ χ
        (rectangularTranslate g Φ) (modelMap σ ℓ v) x h
          ∂generalLinearHaar F.Carrier r := by
  have hweight :
      ((adjacentRankDeterminantWeight F.canonicalTopologicalData χ
        (r + 2) (((r + 1 : ℕ) : ℂ) / 2)).toMonoidHom (upperColumn x * g) : ℂ) =
      ((adjacentRankDeterminantWeight F.canonicalTopologicalData χ
        (r + 2) (((r + 1 : ℕ) : ℂ) / 2)).toMonoidHom g : ℂ) := by
    rw [map_mul, Units.val_mul]
    have hc :
        (adjacentRankDeterminantWeight F.canonicalTopologicalData χ
          (r + 2) (((r + 1 : ℕ) : ℂ) / 2)).toMonoidHom (upperColumn x) = 1 := by
      simp [adjacentRankDeterminantWeight_apply,
        PadicField.TopologicalData.determinantComplexPower,
        F.canonicalTopologicalData.ord_one]
    rw [hc, Units.val_one, one_mul]
  unfold integrand
  rw [sectionCoefficient_normalizedSection, hweight, mul_assoc, ← integral_mul_const]
  apply congrArg (_ * ·)
  apply integral_congr_ae
  filter_upwards with h
  simp only [Units.val_mul, ← Matrix.mul_assoc, rectangularJoin_mul_upperColumn,
    determinantWeight_eq, AdjacentDoubleIntegral.integrand, rectangularTranslate_apply]
  change Φ.val (rectangularJoin h.val (h.val *ᵥ x) * g.val) *
      ((χ (determinant h) : ℂ) *
        determinantWeight abv h (((r + 2 : ℕ) : ℂ) / 2)) *
      ℓ.val (σ h⁻¹ v) * ψ.complex (-x (Fin.last r)) =
    Φ.val (rectangularJoin h.val (h.val *ᵥ x) * g.val) *
      ℓ.val (σ h⁻¹ v) * (χ (determinant h) : ℂ) *
      determinantWeight abv h (((r + 2 : ℕ) : ℂ) / 2) *
      ψ.complex (-x (Fin.last r))
  ring

/-- Actual scalar Jacquet integrability of every pure normalized compact section
uses the same representation-uniform threshold as the double integral. -/
theorem integrable_normalizedSection_realTwist (ν : AdditiveHaarMeasure F.Carrier)
    (hσ : IsOfWhittakerType r (standardCharacter ψ r) σ)
    (χ₀ : Quasicharacter F.Carrier) (u : ℝ)
    (hu : realTwistThreshold F ψ σ hσ ℓ χ₀ < u)
    (Φ : adjacentRankCompactTests (r + 1) F.Carrier) (v : V)
    (g : GeneralLinear (r + 2) F.Carrier) :
    Integrable
      (integrand F ψ σ ℓ (realTwistedCharacter F χ₀ u)
        (Padic.adjacentRankNormalizedSection F σ
          (realTwistedCharacter F χ₀ u) hσ.1.1 Φ v) g)
      (rowMeasure ν (r + 1)) := by
  apply Integrable.congr
    ((AdjacentDoubleIntegral.integrable_realTwist F ν ψ σ hσ ℓ χ₀ u hu
      (modelMap σ ℓ v) (rectangularTranslate g Φ)).integral_prod_left.const_mul
        ((adjacentRankDeterminantWeight F.canonicalTopologicalData
          (realTwistedCharacter F χ₀ u) (r + 2)
            (((r + 1 : ℕ) : ℂ) / 2)).toMonoidHom g : ℂ))
  exact Filter.Eventually.of_forall fun x =>
    (integrand_normalizedSection F ψ σ ℓ _ hσ.1.1 Φ v g x).symm

/-- Scalar integration of a pure normalized section retains the literal
iterated double integral, including its exact outer determinant weight. -/
theorem integral_normalizedSection_eq_doubleIntegral (ν : AdditiveHaarMeasure F.Carrier)
    (hσ : IsSmooth σ)
    (Φ : adjacentRankCompactTests (r + 1) F.Carrier) (v : V)
    (g : GeneralLinear (r + 2) F.Carrier) :
    (∫ x, integrand F ψ σ ℓ χ
      (Padic.adjacentRankNormalizedSection F σ χ hσ Φ v) g x
        ∂rowMeasure ν (r + 1)) =
    ((adjacentRankDeterminantWeight F.canonicalTopologicalData χ
      (r + 2) (((r + 1 : ℕ) : ℂ) / 2)).toMonoidHom g : ℂ) *
      ∫ x, ∫ h, AdjacentDoubleIntegral.integrand F ψ σ ℓ χ
        (rectangularTranslate g Φ) (modelMap σ ℓ v) x h
          ∂generalLinearHaar F.Carrier r ∂rowMeasure ν (r + 1) := by
  simp_rw [integrand_normalizedSection]
  rw [integral_const_mul]

/-- The actual Jacquet integral on each pure original-carrier normalized section
is precisely the published pure-tensor model integral, as a function of every g. -/
theorem integral_normalizedSection_eq_modelIntegral (ν : AdditiveHaarMeasure F.Carrier)
    (hself : IsSelfDual ψ ν)
    (hσ : IsOfWhittakerType r (standardCharacter ψ r) σ)
    (χ₀ : Quasicharacter F.Carrier) (u : ℝ)
    (hu : realTwistThreshold F ψ σ hσ ℓ χ₀ < u)
    (Φ : adjacentRankCompactTests (r + 1) F.Carrier) (v : V)
    (g : GeneralLinear (r + 2) F.Carrier) :
    (∫ x, integrand F ψ σ ℓ (realTwistedCharacter F χ₀ u)
      (Padic.adjacentRankNormalizedSection F σ (realTwistedCharacter F χ₀ u)
        hσ.1.1 Φ v) g x ∂rowMeasure ν (r + 1)) =
    adjacentRankModelIntegral ψ ν hself σ ℓ abv (realTwistedCharacter F χ₀ u)
      (generalLinearHaar F.Carrier r)
      ((partialFourierEquiv ψ ν (r + 1) hself Φ.val) ⊗ₜ[ℂ] (modelMap σ ℓ v)) g := by
  rw [integral_normalizedSection_eq_doubleIntegral, determinantWeight_eq]
  exact AdjacentDoubleIntegral.double_integral_eq_modelIntegral
    F ν ψ hself σ hσ ℓ χ₀ u hu (modelMap σ ℓ v) Φ.val g

end Langlands.RankinSelberg.AdjacentJacquet
