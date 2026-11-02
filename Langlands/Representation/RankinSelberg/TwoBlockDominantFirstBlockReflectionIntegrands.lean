import Langlands.Representation.RankinSelberg.TwoBlockDominantFirstBlockReflectionMeasure
import Langlands.Representation.RankinSelberg.TwoBlockDominantFirstBlockSmallLaurent

/-! # Actual reflected first-block integrands -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.RankinSelberg.TwoBlockDominantFirstBlock

open MeasureTheory GeneralLinear Whittaker HarmonicAnalysis TwoBlockJacquet
  TwoBlockFirstBlockQuotient TwoBlockLowerUnipotentQuotient
  TwoBlockLowerFirstBlockQuotient TwoBlockFirstBlockLaurent
open scoped NNReal

universe uF uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance reflectionIntegrandTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance reflectionIntegrandValuation : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance reflectionIntegrandLocalField : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance reflectionIntegrandT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance reflectionIntegrandCountable : SecondCountableTopology F.Carrier := F.canonicalTopologicalData.secondCountableTopology
local instance reflectionIntegrandMeasurable : MeasurableSpace F.Carrier := borel _
local instance reflectionIntegrandBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance reflectionIntegrandGLMeasurable (a : ℕ) : MeasurableSpace (GeneralLinear a F.Carrier) := borel _
local instance reflectionIntegrandGLBorel (a : ℕ) : BorelSpace (GeneralLinear a F.Carrier) := ⟨rfl⟩
local instance reflectionIntegrandNQMeasurable (a : ℕ) : MeasurableSpace (LeftUnipotentQuotient a F.Carrier) := borel _
local instance reflectionIntegrandNQBorel (a : ℕ) : BorelSpace (LeftUnipotentQuotient a F.Carrier) := ⟨rfl⟩

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1) (j k : ℕ)
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
variable {σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i)}
variable {ψ : UnitaryAdditiveCharacter F.Carrier}
variable (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i)) (f : Sections F h σ)
variable (Wtest : WhittakerFunctions ψ (t + (j + k + 1)))

/-- The actual dual smaller integrand before reflection of its small quotient. -/
def firstBlockDualFiberIntegrand (s : ℂ)
    (Y : Matrix (Fin j) (Fin (m 1 + 1)) F.Carrier)
    (g : GeneralLinear (t + 1) F.Carrier)
    (z : Matrix (Fin k) (Fin (m 0 + 1)) F.Carrier)
    (q : LeftUnipotentQuotient (m 0) F.Carrier) : ℂ :=
  unequalRankIntegrandAt F k (m 1 + 1 + j)
    (by have := firstBlockSmallRank h j k; omega) (ψ.scale (-1))
    (normalizedAbsoluteValue F.canonicalTopologicalData)
    (translateWhittaker (ψ.scale (-1)) (t + (j + k + 1))
      (firstDualFunction ψ (t + (j + k + 1))
        (translateWhittaker ψ (t + (j + k + 1)) Wtest
          (rectangularUnipotent j k (firstBlockColumns h j 0 Y) *
            appendIdentity t (j + k + 1) g)))
      (blockWeylAt (m 0) (t + (j + k + 1)) (firstBlockSmallRank_lt h j k)))
    (secondDualFunction ψ (m 0) (firstBlockCoefficient ell f g).val) s z q

/-- Reflection gives exactly the actual lower test matrix and the original first
coefficient, with the inverse determinant exponent. -/
theorem firstBlockDualFiberIntegrand_reflection (s : ℂ)
    (Y : Matrix (Fin j) (Fin (m 1 + 1)) F.Carrier)
    (g : GeneralLinear (t + 1) F.Carrier)
    (z : Matrix (Fin k) (Fin (m 0 + 1)) F.Carrier)
    (v : GeneralLinear (m 0 + 1) F.Carrier) :
    firstBlockDualFiberIntegrand F h j k ell f Wtest s Y g z
        (reflectionQuotient (m 0) (Quotient.mk _ v)) =
      Wtest.val (TwoBlockDominantRectangular.matrix h rfl
        (firstBlockEmbedding h F.Carrier v * g)
        (firstBlockReflectedRectangle v z) (Y.submatrix Fin.rev Fin.rev)) *
      (firstBlockCoefficient ell f g).val.val v *
      determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) v
        (-(s - ((k + (m 1 + 1 + j) + 1 : ℕ) : ℂ) / 2)) := by
  have hinv : weylLong (m 0 + 1) F.Carrier * inverseTranspose (m 0 + 1) F.Carrier
      (weylLong (m 0 + 1) F.Carrier * inverseTranspose (m 0 + 1) F.Carrier v) = v := by
    rw [map_mul, inverseTranspose_weylLong, inverseTranspose_involutive, ← mul_assoc,
      weylLong_mul_self, one_mul]
  rw [firstBlockDualFiberIntegrand, reflectionQuotient_mk, unequalRankIntegrandAt_mk,
    translateWhittaker_apply, firstDualFunction_apply, translateWhittaker_apply,
    secondDualFunction_apply, firstBlock_reflected_test_matrix h j k, hinv]
  congr 1
  have hr : 0 < normalizedAbsoluteValue F.canonicalTopologicalData (Matrix.det v.val) :=
    (normalizedAbsoluteValue F.canonicalTopologicalData).pos
      ((Matrix.isUnit_iff_isUnit_det _).mp v.isUnit).ne_zero
  rw [determinantWeight, determinantWeight, abv_det_weylLong_mul_inverseTranspose,
    Complex.ofReal_inv, Complex.inv_cpow _ _ (by
      rw [Complex.arg_ofReal_of_nonneg hr.le]
      exact Real.pi_ne_zero.symm), Complex.cpow_neg]

end Langlands.RankinSelberg.TwoBlockDominantFirstBlock
