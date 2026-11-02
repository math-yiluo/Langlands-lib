import Langlands.Representation.RankinSelberg.TwoBlockDominantFirstBlockReflectionCoefficients
import Langlands.Representation.RankinSelberg.TwoBlockDominantFirstBlockRectangleReversal
import Langlands.Representation.RankinSelberg.TwoBlockDominantKernelRegularity

/-! # Convergent reflected first-block averages -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.RankinSelberg.TwoBlockDominantFirstBlock

open MeasureTheory GeneralLinear Whittaker HarmonicAnalysis TwoBlockJacquet
  TwoBlockFirstBlockQuotient TwoBlockLowerUnipotentQuotient
  TwoBlockLowerFirstBlockQuotient TwoBlockFirstBlockLaurent QuotientIntegration

universe uF uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance reflectionAverageTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance reflectionAverageValuation : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance reflectionAverageLocalField : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance reflectionAverageT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance reflectionAverageCountable : SecondCountableTopology F.Carrier := F.canonicalTopologicalData.secondCountableTopology
local instance reflectionAverageMeasurable : MeasurableSpace F.Carrier := borel _
local instance reflectionAverageBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance reflectionAverageMatrixBorel (a b : ℕ) : BorelSpace (Matrix (Fin a) (Fin b) F.Carrier) :=
  inferInstanceAs (BorelSpace (Fin a → Fin b → F.Carrier))
local instance reflectionAverageMatrixCountable (a b : ℕ) : SecondCountableTopology (Matrix (Fin a) (Fin b) F.Carrier) :=
  inferInstanceAs (SecondCountableTopology (Fin a → Fin b → F.Carrier))
local instance reflectionAverageGLMeasurable (a : ℕ) : MeasurableSpace (GeneralLinear a F.Carrier) := borel _
local instance reflectionAverageGLBorel (a : ℕ) : BorelSpace (GeneralLinear a F.Carrier) := ⟨rfl⟩
local instance reflectionAverageGLTopology (a : ℕ) : IsTopologicalGroup (GeneralLinear a F.Carrier) :=
  F.canonicalTopologicalData.generalLinearTopologicalGroup a
local instance reflectionAverageGLCountable (a : ℕ) : SecondCountableTopology (GeneralLinear a F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology a
local instance reflectionAverageNMeasurable (a : ℕ) : MeasurableSpace (upperUnipotent a F.Carrier) := borel _
local instance reflectionAverageNBorel (a : ℕ) : BorelSpace (upperUnipotent a F.Carrier) := ⟨rfl⟩
local instance reflectionAverageNQMeasurable (a : ℕ) : MeasurableSpace (LeftUnipotentQuotient a F.Carrier) := borel _
local instance reflectionAverageNQBorel (a : ℕ) : BorelSpace (LeftUnipotentQuotient a F.Carrier) := ⟨rfl⟩

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1) (j k : ℕ)
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
variable {σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i)}
variable {ψ : UnitaryAdditiveCharacter F.Carrier}
variable (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i)) (f : Sections F h σ)
variable (Wtest : WhittakerFunctions ψ (t + (j + k + 1)))
variable (ν : AdditiveHaarMeasure F.Carrier)

/-- The actual reflected small rectangle average with its spectral factor. -/
def firstBlockReflectedRowAverage (d : ℤ)
    (q : LeftUnipotentQuotient (m 0) F.Carrier)
    (Y : Matrix (Fin j) (Fin (m 1 + 1)) F.Carrier)
    (g : GeneralLinear (t + 1) F.Carrier) : ℂ :=
  determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) g
      (0 - ((j + k + 1 : ℕ) : ℂ) / 2 + (j : ℂ)) *
    (F.canonicalTopologicalData.residueCardinality : ℂ) ^ d *
    ∫ z, firstBlockDualFiberIntegrand F h j k ell f Wtest 0 Y g z
      (reflectionQuotient (m 0) q) ∂rectangularMeasure ν k (m 0 + 1)

/-- The remaining-column norm profile of the actual reflected row average. -/
def firstBlockReflectedColumnNormProfile (d : ℤ)
    (q : LeftUnipotentQuotient (m 0) F.Carrier)
    (g : GeneralLinear (t + 1) F.Carrier) : ℝ :=
  ∫ Y, ‖firstBlockReflectedRowAverage F h j k ell f Wtest ν d q Y g‖
    ∂rectangularMeasure ν j (m 1 + 1)

/-- Joint continuity of the reflected integrand descends through the open
quotient map; its representative formula is the actual lower test matrix. -/
theorem continuous_firstBlockDualFiberIntegrand_reflection
    (hW : Continuous Wtest.val) (hσ : IsSmooth (σ 0))
    (g : GeneralLinear (t + 1) F.Carrier) :
    Continuous (fun z : LeftUnipotentQuotient (m 0) F.Carrier ×
        (Matrix (Fin j) (Fin (m 1 + 1)) F.Carrier ×
          Matrix (Fin k) (Fin (m 0 + 1)) F.Carrier) =>
      firstBlockDualFiberIntegrand F h j k ell f Wtest 0 z.2.1 g z.2.2
        (reflectionQuotient (m 0) z.1)) := by
  apply ((leftQuotient_isOpenQuotientMap (upperUnipotent (m 0 + 1) F.Carrier)).prodMap
    IsOpenQuotientMap.id).isQuotientMap.continuous_iff.mpr
  change Continuous (fun z : GeneralLinear (m 0 + 1) F.Carrier ×
      (Matrix (Fin j) (Fin (m 1 + 1)) F.Carrier ×
        Matrix (Fin k) (Fin (m 0 + 1)) F.Carrier) =>
    firstBlockDualFiberIntegrand F h j k ell f Wtest 0 z.2.1 g z.2.2
      (reflectionQuotient (m 0) (Quotient.mk _ z.1)))
  simp_rw [firstBlockDualFiberIntegrand_reflection]
  have hsmall : Continuous (firstBlockCoefficient ell f g).val.val := by
    obtain ⟨v, hv⟩ := modelMap_surjective (σ 0) (ell 0) (firstBlockCoefficient ell f g)
    rw [← hv]
    exact (matrixCoefficient_isLocallyConstant (σ 0) (ell 0).val v (hσ v)).continuous
  have hx : Continuous (fun z : GeneralLinear (m 0 + 1) F.Carrier ×
      (Matrix (Fin j) (Fin (m 1 + 1)) F.Carrier ×
        Matrix (Fin k) (Fin (m 0 + 1)) F.Carrier) =>
      firstBlockReflectedRectangle z.1 z.2.2) :=
    (continuous_const.matrix_mul (Units.continuous_val.comp continuous_fst)).matrix_mul
      continuous_snd.snd.matrix_transpose
  have hY : Continuous (fun Y : Matrix (Fin j) (Fin (m 1 + 1)) F.Carrier =>
      Y.submatrix Fin.rev Fin.rev) := by fun_prop
  have hm := (TwoBlockDominantRectangular.continuous_matrix h rfl).comp
    ((((continuous_firstBlockEmbedding h F.Carrier).comp continuous_fst).mul_const g).prodMk
      (hx.prodMk (hY.comp continuous_snd.fst)))
  exact ((hW.comp hm).mul (hsmall.comp continuous_fst)).mul
    ((continuous_adjacentRank_determinantWeight F (m 0 + 1)
      (-(0 - ((k + (m 1 + 1 + j) + 1 : ℕ) : ℂ) / 2))).comp continuous_fst)

/-- Joint measurability of the actual quotient/column average needs no
measurable choice of representatives. -/
theorem firstBlockReflectedRowAverage_stronglyMeasurable
    (hW : Continuous Wtest.val) (hσ : IsSmooth (σ 0)) (d : ℤ)
    (g : GeneralLinear (t + 1) F.Carrier) :
    StronglyMeasurable (fun z : LeftUnipotentQuotient (m 0) F.Carrier ×
        Matrix (Fin j) (Fin (m 1 + 1)) F.Carrier =>
      firstBlockReflectedRowAverage F h j k ell f Wtest ν d z.1 z.2 g) := by
  have := TwoBlockLowerUnfolding.sigmaFinite_additiveHaarMeasure ν
  have hi := (continuous_firstBlockDualFiberIntegrand_reflection
    F h j k ell f Wtest hW hσ g).measurable.stronglyMeasurable
  have hm := hi.comp_measurable
    (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
  exact hm.integral_prod_right'.const_mul _

/-- The positive real density in the lower first-block slice tower. -/
def firstBlockReflectionDensity (d : ℤ) : ℝ :=
  (F.canonicalTopologicalData.residueCardinality : ℝ) ^
    (-(d * ((m 1 + 1 : ℕ) : ℤ)))

theorem firstBlockReflectionDensity_nonneg (d : ℤ) :
    0 ≤ firstBlockReflectionDensity F (m := m) d :=
  zpow_nonneg (Nat.cast_nonneg _) _

/-- The exact coefficient calculation at a representative on the small slice. -/
theorem firstBlockReflectedRowAverage_mk_on_slice
    (d : ℤ) (v : GeneralLinear (m 0 + 1) F.Carrier)
    (Y : Matrix (Fin j) (Fin (m 1 + 1)) F.Carrier)
    (g : GeneralLinear (t + 1) F.Carrier)
    (hv : (Quotient.mk _ v : LeftUnipotentQuotient (m 0) F.Carrier) ∈
      RankinSelberg.determinantSlice F.canonicalTopologicalData (m 0) d) :
    firstBlockReflectedRowAverage F h j k ell f Wtest ν d (Quotient.mk _ v) Y g =
      (firstBlockReflectionDensity F (m := m) d : ℂ) *
        ∫ X, TwoBlockDominantRectangular.kernel ell f Wtest rfl 0
          (firstBlockEmbedding h F.Carrier v * g) X (Y.submatrix Fin.rev Fin.rev)
          ∂rectangularMeasure ν (m 0 + 1) k :=
  firstBlockDualFiberIntegral_reflection_on_slice F h j k ell f Wtest ν d Y g v hv

/-- Genuine lower rectangle convergence controls the remaining columns of
the actual reflected average, with the integral of the raw norm retained. -/
theorem firstBlockReflectedRowAverage_column_control
    (d : ℤ) (q : LeftUnipotentQuotient (m 0) F.Carrier)
    (g : GeneralLinear (t + 1) F.Carrier)
    (hq : q ∈ RankinSelberg.determinantSlice F.canonicalTopologicalData (m 0) d)
    (hi : TwoBlockDominantRectangular.quotientFiberIntegrable ν ell f Wtest rfl 0
      (firstBlockFiberPoint F h q g)) :
    Integrable (fun Y => firstBlockReflectedRowAverage F h j k ell f Wtest ν d q Y g)
      (rectangularMeasure ν j (m 1 + 1)) ∧
    firstBlockReflectedColumnNormProfile F h j k ell f Wtest ν d q g ≤
      firstBlockReflectionDensity F (m := m) d *
        TwoBlockDominantRectangular.quotientNormProfile ν ell f Wtest rfl 0
          (firstBlockFiberPoint F h q g) ∧
    (∫ Y, firstBlockReflectedRowAverage F h j k ell f Wtest ν d q Y g
      ∂rectangularMeasure ν j (m 1 + 1)) =
      (firstBlockReflectionDensity F (m := m) d : ℂ) *
        TwoBlockDominantRectangular.quotientKernel ν ell f Wtest rfl 0
          (firstBlockFiberPoint F h q g) := by
  have := TwoBlockLowerUnfolding.sigmaFinite_additiveHaarMeasure ν
  induction q using Quotient.inductionOn with
  | h v =>
    rw [firstBlockFiberPoint_mk] at hi ⊢
    change Integrable
      (fun z : TwoBlockDominantRectangular.Rectangles m j k F.Carrier =>
        TwoBlockDominantRectangular.kernel ell f Wtest rfl 0
          (firstBlockEmbedding h F.Carrier v * g) z.1 z.2)
      ((rectangularMeasure ν (m 0 + 1) k).prod (rectangularMeasure ν j (m 1 + 1))) at hi
    let H := fun Y : Matrix (Fin j) (Fin (m 1 + 1)) F.Carrier =>
      ∫ X, TwoBlockDominantRectangular.kernel ell f Wtest rfl 0
        (firstBlockEmbedding h F.Carrier v * g) X Y
        ∂rectangularMeasure ν (m 0 + 1) k
    have he (Y : Matrix (Fin j) (Fin (m 1 + 1)) F.Carrier) :
        firstBlockReflectedRowAverage F h j k ell f Wtest ν d (Quotient.mk _ v) Y g =
          (firstBlockReflectionDensity F (m := m) d : ℂ) *
            H (Y.submatrix Fin.rev Fin.rev) :=
      firstBlockReflectedRowAverage_mk_on_slice F h j k ell f Wtest ν d v Y g hq
    have hH : Integrable H (rectangularMeasure ν j (m 1 + 1)) :=
      hi.integral_prod_right
    have hHr := (integrable_firstBlockRectangleReversal_iff F.Carrier ν j (m 1 + 1) H).mpr hH
    have hB : Integrable (fun Y =>
        firstBlockReflectedRowAverage F h j k ell f Wtest ν d (Quotient.mk _ v) Y g)
        (rectangularMeasure ν j (m 1 + 1)) := by
      simpa only [he] using hHr.const_mul (firstBlockReflectionDensity F (m := m) d : ℂ)
    refine ⟨hB, ?_, ?_⟩
    · have hn := firstBlockReflectionDensity_nonneg F (m := m) d
      calc
        _ = firstBlockReflectionDensity F (m := m) d *
            ∫ Y, ‖H Y‖ ∂rectangularMeasure ν j (m 1 + 1) := by
          simp only [firstBlockReflectedColumnNormProfile, he, norm_mul,
            Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hn]
          rw [integral_const_mul,
            integral_firstBlockRectangleReversal F.Carrier ν j (m 1 + 1) (fun Y => ‖H Y‖)]
        _ ≤ firstBlockReflectionDensity F (m := m) d *
            ∫ Y, ∫ X, ‖TwoBlockDominantRectangular.kernel ell f Wtest rfl 0
              (firstBlockEmbedding h F.Carrier v * g) X Y‖
                ∂rectangularMeasure ν (m 0 + 1) k
                ∂rectangularMeasure ν j (m 1 + 1) := by
          apply mul_le_mul_of_nonneg_left _ hn
          exact integral_mono hH.norm hi.norm.integral_prod_right
            (fun Y => norm_integral_le_integral_norm _)
        _ = _ := by
          rw [TwoBlockDominantRectangular.quotientNormProfile_mk]
          congr 1
          exact (integral_prod_symm _ hi.norm).symm
    · simp_rw [he]
      rw [integral_const_mul, integral_firstBlockRectangleReversal,
        TwoBlockDominantRectangular.quotientKernel_mk]
      congr 1
      exact (integral_prod_symm _ hi).symm

/-- The actual lower raw norm supplies quotient/column product convergence.
Fubini then identifies the integrated reflected coefficient with the actual
unweighted lower first-block average and its positive density. -/
theorem firstBlockReflectedRowAverage_product_control
    (hW : Continuous Wtest.val) (hσ : IsSmooth (σ 0))
    (μ : Measure (LeftUnipotentQuotient (m 0) F.Carrier)) [SFinite μ]
    (hμ : IsCompatible (upperUnipotent (m 0 + 1) F.Carrier)
      (generalLinearHaar F.Carrier (m 0)) (unipotentHaar F.Carrier (m 0)) μ)
    (hInv : NormOneRightInvariant F (m 0) μ)
    (d : ℤ) (g : GeneralLinear (t + 1) F.Carrier)
    (hrect : ∀ᵐ q ∂μ.restrict
        (RankinSelberg.determinantSlice F.canonicalTopologicalData (m 0) d),
      TwoBlockDominantRectangular.quotientFiberIntegrable ν ell f Wtest rfl 0
        (firstBlockFiberPoint F h q g))
    (hN : Integrable (fun q => TwoBlockDominantRectangular.quotientNormProfile
      ν ell f Wtest rfl 0 (firstBlockFiberPoint F h q g))
      (μ.restrict (RankinSelberg.determinantSlice F.canonicalTopologicalData (m 0) d))) :
    Integrable (fun z : LeftUnipotentQuotient (m 0) F.Carrier ×
        Matrix (Fin j) (Fin (m 1 + 1)) F.Carrier =>
      firstBlockReflectedRowAverage F h j k ell f Wtest ν d z.1 z.2 g)
      ((μ.restrict (RankinSelberg.determinantSlice F.canonicalTopologicalData (m 0) d)).prod
        (rectangularMeasure ν j (m 1 + 1))) ∧
    Integrable (fun Y => firstBlockReflectedSmallCoefficient F h j k ell f Wtest ν μ d Y g)
      (rectangularMeasure ν j (m 1 + 1)) ∧
    (∫ Y, firstBlockReflectedSmallCoefficient F h j k ell f Wtest ν μ d Y g
      ∂rectangularMeasure ν j (m 1 + 1)) =
      (firstBlockReflectionDensity F (m := m) d : ℂ) *
        firstBlockAverage F h μ hInv d
          (TwoBlockDominantRectangular.quotientKernel ν ell f Wtest rfl 0)
          (Quotient.mk _ g) := by
  have := TwoBlockLowerUnfolding.sigmaFinite_additiveHaarMeasure ν
  have hm := firstBlockReflectedRowAverage_stronglyMeasurable F h j k ell f Wtest ν hW hσ d g
  have hmem := ae_restrict_mem (μ := μ)
    (RankinSelberg.measurableSet_determinantSlice F.canonicalTopologicalData (m 0) d)
  have hp : Integrable
      (fun q => firstBlockReflectedColumnNormProfile F h j k ell f Wtest ν d q g)
      (μ.restrict (RankinSelberg.determinantSlice F.canonicalTopologicalData (m 0) d)) := by
    apply (hN.const_mul (firstBlockReflectionDensity F (m := m) d)).mono'
      hm.norm.integral_prod_right'.aestronglyMeasurable
    filter_upwards [hmem, hrect] with q hq hqr
    have hn : 0 ≤ firstBlockReflectedColumnNormProfile F h j k ell f Wtest ν d q g :=
      integral_nonneg (fun _ => norm_nonneg _)
    change ‖firstBlockReflectedColumnNormProfile F h j k ell f Wtest ν d q g‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg hn]
    exact (firstBlockReflectedRowAverage_column_control
      F h j k ell f Wtest ν d q g hq hqr).2.1
  have hi : Integrable (fun z : LeftUnipotentQuotient (m 0) F.Carrier ×
        Matrix (Fin j) (Fin (m 1 + 1)) F.Carrier =>
      firstBlockReflectedRowAverage F h j k ell f Wtest ν d z.1 z.2 g)
      ((μ.restrict (RankinSelberg.determinantSlice F.canonicalTopologicalData (m 0) d)).prod
        (rectangularMeasure ν j (m 1 + 1))) := by
    apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
    refine ⟨?_, hp⟩
    filter_upwards [hmem, hrect] with q hq hqr
    exact (firstBlockReflectedRowAverage_column_control
      F h j k ell f Wtest ν d q g hq hqr).1
  have he (Y : Matrix (Fin j) (Fin (m 1 + 1)) F.Carrier) :
      firstBlockReflectedSmallCoefficient F h j k ell f Wtest ν μ d Y g =
        ∫ q in RankinSelberg.determinantSlice F.canonicalTopologicalData (m 0) d,
          firstBlockReflectedRowAverage F h j k ell f Wtest ν d q Y g ∂μ :=
    firstBlockReflectedSmallCoefficient_eq_sliceIntegral F h j k ell f Wtest ν μ hμ d Y g
  refine ⟨hi, ?_, ?_⟩
  · simpa only [he] using hi.integral_prod_right
  · simp_rw [he]
    rw [← integral_integral_swap hi, TwoBlockLowerFirstBlockQuotient.firstBlockAverage_mk,
      ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hmem, hrect] with q hq hqr
    exact (firstBlockReflectedRowAverage_column_control
      F h j k ell f Wtest ν d q g hq hqr).2.2

end Langlands.RankinSelberg.TwoBlockDominantFirstBlock
