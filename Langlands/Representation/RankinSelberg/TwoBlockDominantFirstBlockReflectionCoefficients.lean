import Langlands.Representation.RankinSelberg.TwoBlockDominantFirstBlockReflectionIntegrands
import Langlands.Representation.RankinSelberg.TwoBlockLowerFirstBlockDensity

/-! # Reflected first-block coefficients and the lower slice density -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.RankinSelberg.TwoBlockDominantFirstBlock

open MeasureTheory GeneralLinear Whittaker HarmonicAnalysis TwoBlockJacquet
  TwoBlockFirstBlockQuotient TwoBlockLowerUnipotentQuotient
  TwoBlockLowerFirstBlockQuotient TwoBlockFirstBlockLaurent
open scoped NNReal

universe uF uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance reflectionCoefficientTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance reflectionCoefficientValuation : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance reflectionCoefficientLocalField : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance reflectionCoefficientT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance reflectionCoefficientCountable : SecondCountableTopology F.Carrier := F.canonicalTopologicalData.secondCountableTopology
local instance reflectionCoefficientMeasurable : MeasurableSpace F.Carrier := borel _
local instance reflectionCoefficientBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance reflectionCoefficientGLMeasurable (a : ℕ) : MeasurableSpace (GeneralLinear a F.Carrier) := borel _
local instance reflectionCoefficientGLBorel (a : ℕ) : BorelSpace (GeneralLinear a F.Carrier) := ⟨rfl⟩
local instance reflectionCoefficientGLTopology (a : ℕ) :
    IsTopologicalGroup (GeneralLinear a F.Carrier) :=
  F.canonicalTopologicalData.generalLinearTopologicalGroup a
local instance reflectionCoefficientNMeasurable (a : ℕ) :
    MeasurableSpace (upperUnipotent a F.Carrier) := borel _
local instance reflectionCoefficientNBorel (a : ℕ) :
    BorelSpace (upperUnipotent a F.Carrier) := ⟨rfl⟩
local instance reflectionCoefficientNQMeasurable (a : ℕ) : MeasurableSpace (LeftUnipotentQuotient a F.Carrier) := borel _
local instance reflectionCoefficientNQBorel (a : ℕ) : BorelSpace (LeftUnipotentQuotient a F.Carrier) := ⟨rfl⟩

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1) (j k : ℕ)
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
variable {σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i)}
variable {ψ : UnitaryAdditiveCharacter F.Carrier}
variable (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i)) (f : Sections F h σ)
variable (Wtest : WhittakerFunctions ψ (t + (j + k + 1)))

variable (ν : AdditiveHaarMeasure F.Carrier)

/-- The actual lower rectangle integral on a first-block representative. -/
def firstBlockLowerRectangleIntegral
    (Y : Matrix (Fin j) (Fin (m 1 + 1)) F.Carrier)
    (g : GeneralLinear (t + 1) F.Carrier)
    (v : GeneralLinear (m 0 + 1) F.Carrier) : ℂ :=
  ∫ X, TwoBlockDominantRectangular.kernel ell f Wtest rfl 0
    (firstBlockEmbedding h F.Carrier v * g) X (Y.submatrix Fin.rev Fin.rev)
    ∂rectangularMeasure ν (m 0 + 1) k

/-- The reflected smaller rectangle integral, including the reciprocal determinant
factor from spectral reflection, is the actual lower rectangle integral times the
positive first-block determinant density. -/
theorem firstBlockDualFiberIntegral_reflection
    (Y : Matrix (Fin j) (Fin (m 1 + 1)) F.Carrier)
    (g : GeneralLinear (t + 1) F.Carrier)
    (v : GeneralLinear (m 0 + 1) F.Carrier) :
    determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) g
        (0 - ((j + k + 1 : ℕ) : ℂ) / 2 + (j : ℂ)) *
      determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) v (-1) *
      (∫ z, firstBlockDualFiberIntegrand F h j k ell f Wtest 0 Y g z
        (reflectionQuotient (m 0) (Quotient.mk _ v))
        ∂rectangularMeasure ν k (m 0 + 1)) =
    determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) v
        ((m 1 + 1 : ℕ) : ℂ) *
      ∫ X, TwoBlockDominantRectangular.kernel ell f Wtest rfl 0
        (firstBlockEmbedding h F.Carrier v * g) X (Y.submatrix Fin.rev Fin.rev)
        ∂rectangularMeasure ν (m 0 + 1) k := by
  simp_rw [firstBlockDualFiberIntegrand_reflection]
  rw [integral_firstBlockReflectedRectangle F ν v
    (fun X => Wtest.val (TwoBlockDominantRectangular.matrix h rfl
      (firstBlockEmbedding h F.Carrier v * g) X (Y.submatrix Fin.rev Fin.rev)) *
      (firstBlockCoefficient ell f g).val.val v *
      determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) v
        (-(0 - ((k + (m 1 + 1 + j) + 1 : ℕ) : ℂ) / 2)))]
  rw [NNReal.smul_def, Complex.real_smul, firstBlockRowJacobian F k v]
  simp_rw [TwoBlockDominantRectangular.kernel_eq,
    scalarSection_firstBlockEmbedding_mul, inv_leviHalfModulus_blockPair_one,
    determinantWeight_mul, determinantWeight_firstBlockEmbedding]
  rw [integral_mul_const, integral_mul_const, integral_mul_const, integral_const_mul]
  have hw :
      determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) v (-1) *
        determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) v (-(k : ℂ)) *
        determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) v
          (-(0 - ((k + (m 1 + 1 + j) + 1 : ℕ) : ℂ) / 2)) =
      determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) v
          ((m 1 + 1 : ℕ) : ℂ) *
        determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) v
          (-(((m 1 + 1 : ℕ) : ℂ) / 2)) *
        determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) v
          (0 - ((j + k + 1 : ℕ) : ℂ) / 2 + (j : ℂ)) := by
    rw [← determinantWeight_add, ← determinantWeight_add,
      ← determinantWeight_add, ← determinantWeight_add]
    congr 1
    push_cast
    ring
  calc
    _ = (determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) v (-1) *
        determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) v (-(k : ℂ)) *
        determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) v
          (-(0 - ((k + (m 1 + 1 + j) + 1 : ℕ) : ℂ) / 2))) *
        (determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) g
          (0 - ((j + k + 1 : ℕ) : ℂ) / 2 + (j : ℂ)) *
          (firstBlockCoefficient ell f g).val.val v *
          ∫ X, Wtest.val (TwoBlockDominantRectangular.matrix h rfl
            (firstBlockEmbedding h F.Carrier v * g) X (Y.submatrix Fin.rev Fin.rev))
            ∂rectangularMeasure ν (m 0 + 1) k) := by ring
    _ = _ := by rw [hw]; ring

/-- On a small determinant slice, the spectral-reflection factor is the
reciprocal determinant and the density is its positive b-th power. -/
theorem firstBlockDualFiberIntegral_reflection_on_slice
    (d : ℤ) (Y : Matrix (Fin j) (Fin (m 1 + 1)) F.Carrier)
    (g : GeneralLinear (t + 1) F.Carrier)
    (v : GeneralLinear (m 0 + 1) F.Carrier)
    (hv : (Quotient.mk _ v : LeftUnipotentQuotient (m 0) F.Carrier) ∈
      RankinSelberg.determinantSlice F.canonicalTopologicalData (m 0) d) :
    determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) g
        (0 - ((j + k + 1 : ℕ) : ℂ) / 2 + (j : ℂ)) *
      (F.canonicalTopologicalData.residueCardinality : ℂ) ^ d *
      (∫ z, firstBlockDualFiberIntegrand F h j k ell f Wtest 0 Y g z
        (reflectionQuotient (m 0) (Quotient.mk _ v))
        ∂rectangularMeasure ν k (m 0 + 1)) =
    (((F.canonicalTopologicalData.residueCardinality : ℝ) ^
      (-(d * ((m 1 + 1 : ℕ) : ℤ))) : ℝ) : ℂ) *
      ∫ X, TwoBlockDominantRectangular.kernel ell f Wtest rfl 0
        (firstBlockEmbedding h F.Carrier v * g) X (Y.submatrix Fin.rev Fin.rev)
        ∂rectangularMeasure ν (m 0 + 1) k := by
  have hdet := (mk_mem_determinantSlice_iff_normalizedAbs F.canonicalTopologicalData).mp hv
  have href : determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) v (-1) =
      (F.canonicalTopologicalData.residueCardinality : ℂ) ^ d := by
    rw [determinantWeight, Complex.cpow_neg_one]
    change ((F.canonicalTopologicalData.normalizedAbs
      (GeneralLinear.determinant v : F.Carrier)) : ℂ)⁻¹ = _
    rw [hdet, Complex.ofReal_zpow, Complex.ofReal_natCast, zpow_neg, inv_inv]
  have hdensity : determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) v
      ((m 1 + 1 : ℕ) : ℂ) =
      (((F.canonicalTopologicalData.residueCardinality : ℝ) ^
        (-(d * ((m 1 + 1 : ℕ) : ℤ))) : ℝ) : ℂ) := by
    rw [determinantWeight, Complex.cpow_natCast]
    change ((F.canonicalTopologicalData.normalizedAbs
      (GeneralLinear.determinant v : F.Carrier)) : ℂ) ^ (m 1 + 1) = _
    rw [hdet, ← Complex.ofReal_pow, ← zpow_natCast, ← zpow_mul]
    congr 2
    ring
  simpa only [href, hdensity] using
    firstBlockDualFiberIntegral_reflection F h j k ell f Wtest ν Y g v

/-- Reflect the actual small quotient slice while retaining its supplied
compatible measure. This step changes no order of integration. -/
theorem firstBlockReflectedSmallCoefficient_eq_sliceIntegral
    (μ : Measure (LeftUnipotentQuotient (m 0) F.Carrier))
    (hμ : QuotientIntegration.IsCompatible (upperUnipotent (m 0 + 1) F.Carrier)
      (generalLinearHaar F.Carrier (m 0)) (unipotentHaar F.Carrier (m 0)) μ)
    (d : ℤ) (Y : Matrix (Fin j) (Fin (m 1 + 1)) F.Carrier)
    (g : GeneralLinear (t + 1) F.Carrier) :
    firstBlockReflectedSmallCoefficient F h j k ell f Wtest ν μ d Y g =
      ∫ q in RankinSelberg.determinantSlice F.canonicalTopologicalData (m 0) d,
        determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) g
          (0 - ((j + k + 1 : ℕ) : ℂ) / 2 + (j : ℂ)) *
        (F.canonicalTopologicalData.residueCardinality : ℂ) ^ d *
        (∫ z, firstBlockDualFiberIntegrand F h j k ell f Wtest 0 Y g z
          (reflectionQuotient (m 0) q) ∂rectangularMeasure ν k (m 0 + 1)) ∂μ := by
  rw [firstBlockReflectedSmallCoefficient, reflectSeries_apply,
    unequalRankSliceCoefficientAt_eq_integral,
    setIntegral_determinantSlice_reflectionQuotient F (m 0) (-d) μ hμ, neg_neg,
    integral_const_mul]
  simp only [firstBlockDualFiberIntegrand, mul_assoc]

end Langlands.RankinSelberg.TwoBlockDominantFirstBlock
