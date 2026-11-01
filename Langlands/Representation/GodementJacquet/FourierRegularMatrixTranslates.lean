import Langlands.Representation.GodementJacquet.FourierRegularMatrixTests
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonFourierTransport

/-! # Invertible translations of Fourier-regular matrix tests -/

noncomputable section

namespace Langlands.GodementJacquet

open HarmonicAnalysis MeasureTheory
open scoped NNReal

universe uF

section General

variable {K : Type uF} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  {d : ℕ}

/-- Invertible left-right multiplication preserves singular vanishing. -/
theorem leftRightTranslate_mem_regularMatrixTests
    (A B : GeneralLinear d K)
    {Φ : SchwartzBruhat (Matrix (Fin d) (Fin d) K)}
    (hΦ : Φ ∈ regularMatrixTests (K := K) d) :
    rectangularLeftRightTranslate A B Φ ∈ regularMatrixTests (K := K) d := by
  intro X hX
  apply hΦ
  intro h
  apply hX
  change IsUnit (A.val * X * B.val) at h
  simpa only [Units.isUnit_mul_units, Units.isUnit_units_mul] using h

/-- Pullback by actual left-right multiplication on regular full-matrix tests. -/
def regularMatrixTranslate (A B : GeneralLinear d K) :
    regularMatrixTests (K := K) d →ₗ[ℂ] regularMatrixTests (K := K) d where
  toFun Φ := ⟨rectangularLeftRightTranslate A B Φ.val,
    leftRightTranslate_mem_regularMatrixTests A B Φ.property⟩
  map_add' Φ Ψ := Subtype.ext ((rectangularLeftRightTranslate A B).map_add Φ.val Ψ.val)
  map_smul' c Φ := Subtype.ext ((rectangularLeftRightTranslate A B).map_smul c Φ.val)

@[simp] theorem regularMatrixTranslate_apply (A B : GeneralLinear d K)
    (Φ : regularMatrixTests (K := K) d) (X : Matrix (Fin d) (Fin d) K) :
    (regularMatrixTranslate A B Φ).val X = Φ.val (A.val * X * B.val) := rfl

end General

namespace Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance translatesTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance translatesValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance translatesLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance translatesT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance translatesDisconnected : TotallyDisconnectedSpace F.Carrier := by
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance translatesMeasurable : MeasurableSpace F.Carrier := borel _
local instance translatesBorel : BorelSpace F.Carrier := ⟨rfl⟩

variable {d : ℕ}

/-- Arbitrary invertible translates preserve both actual singular-vanishing
conditions. The Fourier change of variables retains its Haar-scaling factor. -/
theorem leftRightTranslate_mem_fourierRegularMatrixTests
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν) (A B : GeneralLinear d F.Carrier)
    {Φ : SchwartzBruhat (Matrix (Fin d) (Fin d) F.Carrier)}
    (hΦ : Φ ∈ fourierRegularMatrixTests d ψ ν hsd) :
    rectangularLeftRightTranslate A B Φ ∈ fourierRegularMatrixTests d ψ ν hsd := by
  refine ⟨leftRightTranslate_mem_regularMatrixTests A B hΦ.1, ?_⟩
  intro X hX
  change rectangularFourierEquiv ψ ν d d hsd
    (rectangularLeftRightTranslate A B Φ) X = 0
  rw [rectangularFourierEquiv_apply]
  let T := F.canonicalTopologicalData
  let := T.secondCountableTopology
  let c : ℝ≥0 :=
    (((T.determinantNorm d A : ℝ≥0) ^ d /
      (T.determinantNorm d B⁻¹ : ℝ≥0) ^ d)⁻¹)
  have hm : (RankinSelberg.rectangularMeasure ν d d).map
      (rectangularLeftRightHomeomorph A B) =
      c • RankinSelberg.rectangularMeasure ν d d := by
    change (RankinSelberg.rectangularMeasure ν d d).map
      (fun X => A.val * X * B.val) = c • RankinSelberg.rectangularMeasure ν d d
    simpa only [inv_inv] using padicRectangularHaarScaling F T d d
      (RankinSelberg.rectangularMeasure ν d d) A B⁻¹
  change rectangularFourierIntegral ψ ν (fun Y => Φ (A.val * Y * B.val)) X = 0
  rw [rectangularFourierIntegral_leftRight ψ ν A B c hm]
  have hz := hΦ.2
    ((GeneralLinear.inverseTranspose d F.Carrier A).val * X *
      (GeneralLinear.inverseTranspose d F.Carrier B).val)
    (by
      intro h
      apply hX
      simpa only [Units.isUnit_mul_units, Units.isUnit_units_mul] using h)
  change rectangularFourierEquiv ψ ν d d hsd Φ _ = 0 at hz
  rw [rectangularFourierEquiv_apply] at hz
  rw [hz, mul_zero]

/-- Actual invertible left-right translation on Fourier-regular tests. -/
def fourierRegularMatrixTranslate
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν) (A B : GeneralLinear d F.Carrier) :
    fourierRegularMatrixTests d ψ ν hsd →ₗ[ℂ]
      fourierRegularMatrixTests d ψ ν hsd where
  toFun Φ := ⟨rectangularLeftRightTranslate A B Φ.val,
    leftRightTranslate_mem_fourierRegularMatrixTests F ψ ν hsd A B Φ.property⟩
  map_add' Φ Ψ := Subtype.ext ((rectangularLeftRightTranslate A B).map_add Φ.val Ψ.val)
  map_smul' c Φ := Subtype.ext ((rectangularLeftRightTranslate A B).map_smul c Φ.val)

@[simp] theorem fourierRegularMatrixTranslate_apply
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν) (A B : GeneralLinear d F.Carrier)
    (Φ : fourierRegularMatrixTests d ψ ν hsd)
    (X : Matrix (Fin d) (Fin d) F.Carrier) :
    (fourierRegularMatrixTranslate F ψ ν hsd A B Φ).val X =
      Φ.val (A.val * X * B.val) := rfl

end Padic

end Langlands.GodementJacquet
