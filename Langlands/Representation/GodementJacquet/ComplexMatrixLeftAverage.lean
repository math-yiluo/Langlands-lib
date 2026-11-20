import Langlands.Representation.GodementJacquet.ComplexMatrixCompactAverage
import Langlands.Representation.Archimedean.TransposePairingRestriction
import Langlands.HarmonicAnalysis.SquareFourierCrossExchange

/-! # Left averaging of matrix Schwartz tests by inverse unitary translations -/

noncomputable section

open MeasureTheory Topology
open scoped Matrix.Norms.Elementwise

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GodementJacquet

open Langlands.Archimedean Langlands.GeneralLinear Langlands.HarmonicAnalysis
open Langlands.LocalFactor.Archimedean
open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal

variable {n : ℕ}
local notation "I" => Fin n
local notation "M" => Matrix I I ℂ
local notation "G" => GeneralLinear n ℂ
local notation "Kc" => unitaryCompact ℂ n
local notation "ι" => inverseTranspose n ℂ

local instance leftAverageGLMeasurable (m : ℕ) : MeasurableSpace (GeneralLinear m ℂ) := borel _
local instance leftAverageGLBorel (m : ℕ) : BorelSpace (GeneralLinear m ℂ) := ⟨rfl⟩
local instance leftAverageGLSecondCountable (m : ℕ) : SecondCountableTopology (GeneralLinear m ℂ) :=
  (RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℂ) m).isInducing.secondCountableTopology
local instance leftAverageUnitarySecondCountable (m : ℕ) :
    SecondCountableTopology (unitaryCompact ℂ m) := IsInducing.subtypeVal.secondCountableTopology
local instance leftAverageScalarHaar (a : ℂˣ) : (complexSelfDualMeasure a).measure.IsAddHaarMeasure :=
  (complexSelfDualMeasure a).isAddHaar

private theorem inverseTranspose_mem_unitary (k : Kc) : ι k.val ∈ Kc := by
  let u : Matrix.unitaryGroup I ℂ := ⟨k.val.val, k.property⟩
  have hu : Unitary.toUnits u = k.val := Units.ext rfl
  rw [← hu, inverseTranspose_unitaryToUnits]
  exact (compactIota ℂ n u).property

/-- Inverse transpose restricts to an involution of the unitary group. -/
def unitaryInverseTranspose : Kc ≃ₜ Kc where
  toFun k := ⟨ι k.val, inverseTranspose_mem_unitary k⟩
  invFun k := ⟨ι k.val, inverseTranspose_mem_unitary k⟩
  left_inv k := Subtype.ext (inverseTranspose_involutive n ℂ k.val)
  right_inv k := Subtype.ext (inverseTranspose_involutive n ℂ k.val)
  continuous_toFun := ((continuous_inverseTranspose n ℂ).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((continuous_inverseTranspose n ℂ).comp continuous_subtype_val).subtype_mk _

theorem unitaryInverseTranspose_val (k : Kc) : (unitaryInverseTranspose k).val = ι k.val := rfl

private def transposeMatrixCLE : M ≃L[ℝ] M where
  toFun := Matrix.transpose
  invFun := Matrix.transpose
  left_inv := Matrix.transpose_transpose
  right_inv := Matrix.transpose_transpose
  map_add' := Matrix.transpose_add
  map_smul' := Matrix.transpose_smul
  continuous_toFun := continuous_id.matrix_transpose
  continuous_invFun := continuous_id.matrix_transpose

private abbrev transposeTest (Φ : SchwartzMap M ℂ) : SchwartzMap M ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ transposeMatrixCLE Φ

private theorem transposeTest_apply (Φ : SchwartzMap M ℂ) (X : M) :
    transposeTest Φ X = Φ X.transpose := rfl

private theorem complexMatrixFourier_transposeTest (a : ℂˣ) (Φ : SchwartzMap M ℂ) (X : M) :
    complexMatrixFourier a (transposeTest Φ) X = complexMatrixFourier a Φ X.transpose :=
  rectangularFourierIntegral_transpose (complexScaledCharacter a) (complexSelfDualMeasure a) Φ X

private theorem integrable_inverseTransposeWeight (μK : Measure Kc) {κ : Kc → ℂ}
    (hκ : Integrable κ μK) :
    Integrable (κ ∘ unitaryInverseTranspose) (μK.map unitaryInverseTranspose) := by
  refine (integrable_map_equiv unitaryInverseTranspose.toMeasurableEquiv _).mpr ?_
  have he : (κ ∘ unitaryInverseTranspose) ∘ unitaryInverseTranspose = κ := by
    funext k
    exact congrArg κ (unitaryInverseTranspose.left_inv k)
  rw [show (κ ∘ ⇑unitaryInverseTranspose) ∘ ⇑unitaryInverseTranspose.toMeasurableEquiv = κ from he]
  exact hκ

/-- Average a Schwartz test over inverse left unitary translations. -/
def complexMatrixInverseLeftAverage (μK : Measure Kc) (κ : Kc → ℂ) (hκ : Integrable κ μK)
    (Φ : SchwartzMap M ℂ) : SchwartzMap M ℂ :=
  transposeTest (complexMatrixCompactAverage (μK.map unitaryInverseTranspose)
    (κ ∘ unitaryInverseTranspose) (integrable_inverseTransposeWeight μK hκ) (transposeTest Φ))

theorem complexMatrixInverseLeftAverage_apply (μK : Measure Kc) (κ : Kc → ℂ)
    (hκ : Integrable κ μK) (Φ : SchwartzMap M ℂ) (X : M) :
    complexMatrixInverseLeftAverage μK κ hκ Φ X = ∫ k, κ k * Φ ((k.val⁻¹).val * X) ∂μK := by
  rw [complexMatrixInverseLeftAverage, transposeTest_apply, complexMatrixCompactAverage_apply]
  let e := (unitaryInverseTranspose (n := n)).toMeasurableEquiv
  change (∫ k : Kc, κ (unitaryInverseTranspose k) *
    transposeTest Φ (X.transpose * k.val.val) ∂μK.map e) = _
  rw [integral_map_equiv e]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun k => by
    change κ (unitaryInverseTranspose (unitaryInverseTranspose k)) *
      Φ (X.transpose * (ι k.val).val).transpose = _
    have hk : unitaryInverseTranspose (unitaryInverseTranspose k) = k := unitaryInverseTranspose.left_inv k
    rw [hk, Matrix.transpose_mul, inverseTranspose_coe,
      Matrix.transpose_transpose, Matrix.transpose_transpose]

/-- Fourier covariance of the inverse left unitary average. -/
theorem complexMatrixFourier_inverseLeftAverage (a : ℂˣ) (μK : Measure Kc) [SFinite μK]
    (κ : Kc → ℂ) (hκ : Integrable κ μK) (hκc : Continuous κ) (Φ : SchwartzMap M ℂ) (X : M) :
    complexMatrixFourier a (complexMatrixInverseLeftAverage μK κ hκ Φ) X =
      ∫ k, κ k * complexMatrixFourier a Φ (((ι k.val)⁻¹).val * X) ∂μK := by
  rw [complexMatrixInverseLeftAverage, complexMatrixFourier_transposeTest,
    complexMatrixFourier_compactAverage _ _ _ _ (hκc.comp unitaryInverseTranspose.continuous)]
  let e := (unitaryInverseTranspose (n := n)).toMeasurableEquiv
  change (∫ k : Kc, κ (unitaryInverseTranspose k) *
    complexMatrixFourier a (transposeTest Φ) (X.transpose * (ι k.val).val) ∂μK.map e) = _
  rw [integral_map_equiv e]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun k => by
    change κ (unitaryInverseTranspose (unitaryInverseTranspose k)) *
      complexMatrixFourier a (transposeTest Φ) (X.transpose * (ι (ι k.val)).val) =
        κ k * complexMatrixFourier a Φ (((ι k.val)⁻¹).val * X)
    have hk : unitaryInverseTranspose (unitaryInverseTranspose k) = k := unitaryInverseTranspose.left_inv k
    rw [hk, complexMatrixFourier_transposeTest, Matrix.transpose_mul,
      Matrix.transpose_transpose, inverseTranspose_involutive, ← map_inv, inverseTranspose_coe, inv_inv]

end Langlands.GodementJacquet
