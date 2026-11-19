import Langlands.Representation.Archimedean.ComplexPartialJacquet
import Langlands.Representation.GodementJacquet.TwoBlockDualParabolicIntegral
import Langlands.Representation.RankinSelberg.GeneralLinearUnimodularity
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonGLDensity
import Langlands.HarmonicAnalysis.FiniteProductMeasureScaling

/-! # Haar measure on the complex general linear group from matrix Lebesgue measure -/

noncomputable section

open MeasureTheory Measure
open scoped NNReal ENNReal Matrix.Norms.Operator

namespace Langlands.Archimedean.ComplexGeneralLinearHaarDensity

open Langlands.GeneralLinear
open Langlands.RankinSelberg.GLDeterminantDensity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear n ℂ) := borel _
local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear n ℂ) := ⟨rfl⟩
local instance (n : ℕ) : SecondCountableTopology (Langlands.GeneralLinear n ℂ) :=
  Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology

private abbrev Square (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

/-- The normalized absolute value of a complex scalar, with values in the nonnegative reals. -/
def normSqHom : ℂ →*₀ ℝ≥0 where
  toFun z := ‖z‖₊ ^ 2
  map_zero' := by simp
  map_one' := by simp
  map_mul' z w := by rw [nnnorm_mul, mul_pow]

theorem continuous_normSqHom : Continuous normSqHom := continuous_nnnorm.pow 2

private def complexLebesgue : Langlands.HarmonicAnalysis.AdditiveHaarMeasure ℂ where
  measure := volume
  isAddHaar := inferInstance
  regular := inferInstance

local instance : SigmaFinite complexLebesgue.measure :=
  inferInstanceAs (SigmaFinite (volume : Measure ℂ))

/-- Product Lebesgue measure on the complex matrix entries. -/
def matrixLebesgue (n : ℕ) : Measure (Square n) :=
  Langlands.RankinSelberg.rectangularMeasure complexLebesgue n n

instance (n : ℕ) : IsAddHaarMeasure (matrixLebesgue n) :=
  Langlands.RankinSelberg.rectangularMeasure_isAddHaar complexLebesgue n n

private theorem map_right_volume {n : ℕ} {B : Square n} (hB : B.det ≠ 0) :
    (matrixLebesgue n).map (fun X => X * B) =
      ((normSqHom B.det)⁻¹ ^ n) • matrixLebesgue n := by
  let e := ComplexPartialJacquet.vecMulEquiv hB
  let c := (normSqHom B.det)⁻¹
  have he : (volume : Measure (Fin n → ℂ)).map e = c • volume := by
    rw [ComplexPartialJacquet.map_vecMulEquiv hB]
    change ENNReal.ofReal ((‖B.det‖ ^ 2)⁻¹) • (volume : Measure (Fin n → ℂ)) =
      (c : ℝ≥0∞) • volume
    rw [← ENNReal.ofReal_coe_nnreal]
    rfl
  change (Measure.pi (fun _ : Fin n => (volume : Measure (Fin n → ℂ)))).map
      (fun (X : Fin n → Fin n → ℂ) i => e (X i)) =
    c ^ n • Measure.pi (fun _ : Fin n => (volume : Measure (Fin n → ℂ)))
  rw [Measure.pi_map_pi (hμ := fun _ => e.sigmaFinite_map) (fun _ => e.measurable.aemeasurable)]
  simp_rw [he]
  rw [Langlands.HarmonicAnalysis.pi_nnreal_smul, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

private theorem map_transpose_volume (n : ℕ) :
    (matrixLebesgue n).map Matrix.transpose = matrixLebesgue n :=
  (Langlands.GodementJacquet.measurePreserving_transpose_rectangularMeasure complexLebesgue n n).map_eq

/-- Left matrix multiplication changes matrix Lebesgue measure by `|det g|_ℂ ^ (-n)`. -/
theorem map_left_volume {n : ℕ} (g : Langlands.GeneralLinear n ℂ) :
    (matrixLebesgue n).map (fun X => g.val * X) =
      weight n normSqHom g • matrixLebesgue n := by
  let μ := matrixLebesgue n
  have htr : Measurable (Matrix.transpose : Square n → Square n) :=
    continuous_id.matrix_transpose.measurable
  have hr : Measurable (fun X : Square n => X * g.val.transpose) :=
    (continuous_id.matrix_mul continuous_const).measurable
  have hs : μ.map (fun X : Square n => X * g.val.transpose) = weight n normSqHom g • μ := by
    rw [map_right_volume (B := g.val.transpose) (by rw [Matrix.det_transpose]; exact g.det_ne_zero),
      Matrix.det_transpose, weight_eq]
  change μ.map (fun X => g.val * X) = weight n normSqHom g • μ
  calc
    _ = ((μ.map Matrix.transpose).map (fun X : Square n => X * g.val.transpose)).map
        Matrix.transpose := by
      rw [Measure.map_map hr htr, Measure.map_map htr (hr.comp htr)]
      simp only [Function.comp_def, Matrix.transpose_mul, Matrix.transpose_transpose]
    _ = _ := by
      rw [map_transpose_volume n, hs, Measure.map_smul _ htr.aemeasurable, map_transpose_volume n]

/-- Multiplicative Haar measure with density `|det g|_ℂ ^ (-n)` against matrix Lebesgue measure
on the invertible locus. -/
def complexGeneralLinearHaar (n : ℕ) : Measure (Langlands.GeneralLinear n ℂ) :=
  weightedRestriction n normSqHom (matrixLebesgue n)

instance (n : ℕ) : IsHaarMeasure (complexGeneralLinearHaar n) :=
  weightedRestriction_isHaar n normSqHom continuous_normSqHom (matrixLebesgue n) map_left_volume

/-- Absolute integrability on the group is equivalent to absolute integrability on the
invertible matrix locus after multiplication by the inverse determinant density. -/
theorem integrable_complexGeneralLinearHaar_iff {n : ℕ} (f : Square n → ℂ) :
    Integrable (fun g : Langlands.GeneralLinear n ℂ => f g.val) (complexGeneralLinearHaar n) ↔
      Integrable (fun X => matrixWeight n normSqHom X • f X)
        ((matrixLebesgue n).restrict (Set.range (Units.val : Langlands.GeneralLinear n ℂ → Square n))) :=
  integrable_weightedRestriction_iff n normSqHom continuous_normSqHom (matrixLebesgue n) f

instance (n : ℕ) : IsMulRightInvariant (complexGeneralLinearHaar n) := by
  let ν := complexGeneralLinearHaar n
  have hscalar (a : ℂˣ) :
      Measure.modularCharacter (GeneralLinear.scalar (n := n) a) = 1 := by
    change Measure.modularCharacterFun _ = 1
    rw [Measure.modularCharacterFun_eq_haarScalarFactor ν]
    have he : (fun x : Langlands.GeneralLinear n ℂ => x * GeneralLinear.scalar a) =
        (fun x : Langlands.GeneralLinear n ℂ => GeneralLinear.scalar a * x) := by
      funext x
      exact (Matrix.GeneralLinearGroup.scalar_commute a x).symm
    simp only [he, map_mul_left_eq_self, Measure.haarScalarFactor_self]
  have htrivial (g : Langlands.GeneralLinear n ℂ) : Measure.modularCharacterFun g = 1 :=
    RankinSelberg.GeneralLinearUnimodularity.character_eq_one Measure.modularCharacter hscalar g
  refine ⟨fun g => ?_⟩
  change (ν.map (fun x => x * g)) = ν
  rw [Measure.isMulLeftInvariant_eq_smul (ν.map (fun x => x * g)) ν,
    ← Measure.modularCharacterFun_eq_haarScalarFactor ν, htrivial, one_smul]

end Langlands.Archimedean.ComplexGeneralLinearHaarDensity
