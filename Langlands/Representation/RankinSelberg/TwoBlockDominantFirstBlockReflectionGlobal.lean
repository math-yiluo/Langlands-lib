import Langlands.Representation.RankinSelberg.TwoBlockDominantFirstBlockReflectionAverages
import Langlands.Representation.RankinSelberg.TwoBlockLowerFirstBlockSliceAnalysis
import Langlands.Representation.RankinSelberg.TwoBlockLowerFirstBlockSliceTower

/-! # Global reflected first-block slice averages -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.RankinSelberg.TwoBlockDominantFirstBlock

open MeasureTheory ProbabilityTheory GeneralLinear Whittaker HarmonicAnalysis TwoBlockJacquet
  TwoBlockFirstBlockQuotient TwoBlockLowerFirstBlockQuotient TwoBlockFirstBlockLaurent
  QuotientIntegration TwoBlockLowerUnipotentQuotient
open scoped ENNReal

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance reflectionGlobalTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance reflectionGlobalValuation : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance reflectionGlobalLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance reflectionGlobalT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance reflectionGlobalCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance reflectionGlobalGLTopology (a : ℕ) : IsTopologicalGroup (GeneralLinear a F.Carrier) :=
  F.canonicalTopologicalData.generalLinearTopologicalGroup a
local instance reflectionGlobalGLCountable (a : ℕ) : SecondCountableTopology (GeneralLinear a F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology a
local instance reflectionGlobalMeasurable : MeasurableSpace F.Carrier := borel _
local instance reflectionGlobalBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance reflectionGlobalGLMeasurable (a : ℕ) : MeasurableSpace (GeneralLinear a F.Carrier) := borel _
local instance reflectionGlobalGLBorel (a : ℕ) : BorelSpace (GeneralLinear a F.Carrier) := ⟨rfl⟩
local instance reflectionGlobalNMeasurable (a : ℕ) :
    MeasurableSpace (upperUnipotent a F.Carrier) := borel _
local instance reflectionGlobalNBorel (a : ℕ) : BorelSpace (upperUnipotent a F.Carrier) := ⟨rfl⟩
local instance reflectionGlobalNCountable (a : ℕ) :
    SecondCountableTopology (upperUnipotent a F.Carrier) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance reflectionGlobalNQMeasurable (a : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient a F.Carrier) := borel _
local instance reflectionGlobalNQBorel (a : ℕ) :
    BorelSpace (LeftUnipotentQuotient a F.Carrier) := ⟨rfl⟩

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1) (j k : ℕ)
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
variable {σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i)}
variable {ψ : UnitaryAdditiveCharacter F.Carrier}
variable (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i)) (f : Sections F h σ)
variable (Wtest : WhittakerFunctions ψ (t + (j + k + 1)))
variable (ν : AdditiveHaarMeasure F.Carrier)

local instance reflectionGlobalHQMeasurable :
    MeasurableSpace (TwoBlockUnipotentQuotient.BlockQuotient h F.Carrier) := borel _
local instance reflectionGlobalHQBorel :
    BorelSpace (TwoBlockUnipotentQuotient.BlockQuotient h F.Carrier) := ⟨rfl⟩
local instance reflectionGlobalHMeasurable :
    MeasurableSpace (TwoBlockUnipotentQuotient.blockUnipotent h F.Carrier) := borel _
local instance reflectionGlobalHBorel :
    BorelSpace (TwoBlockUnipotentQuotient.blockUnipotent h F.Carrier) := ⟨rfl⟩
local instance reflectionGlobalMixedSubgroupMeasurable :
    MeasurableSpace (mixedSubgroup F h) := borel _
local instance reflectionGlobalMixedSubgroupBorel : BorelSpace (mixedSubgroup F h) := ⟨rfl⟩
local instance reflectionGlobalLowerMixedSubgroupMeasurable :
    MeasurableSpace (lowerMixedSubgroup F h) := borel _
local instance reflectionGlobalLowerMixedSubgroupBorel : BorelSpace (lowerMixedSubgroup F h) := ⟨rfl⟩
local instance reflectionGlobalMixedMeasurable :
    MeasurableSpace (MixedQuotient F h) := borel _
local instance reflectionGlobalMixedBorel : BorelSpace (MixedQuotient F h) := ⟨rfl⟩
local instance reflectionGlobalLowerMixedMeasurable :
    MeasurableSpace (LowerMixedQuotient F h) := borel _
local instance reflectionGlobalLowerMixedBorel : BorelSpace (LowerMixedQuotient F h) := ⟨rfl⟩

local instance reflectionGlobalGLLocallyCompact (a : ℕ) : LocallyCompactSpace (GeneralLinear a F.Carrier) :=
  F.canonicalTopologicalData.generalLinearLocallyCompactSpace a
local instance reflectionGlobalLowerMeasurable : MeasurableSpace (LowerQuotient h F.Carrier) := borel _
local instance reflectionGlobalLowerBorel : BorelSpace (LowerQuotient h F.Carrier) := ⟨rfl⟩
local instance reflectionGlobalLowerHMeasurable :
    MeasurableSpace (lowerBlockUnipotent h F.Carrier) := borel _
local instance reflectionGlobalLowerHBorel :
    BorelSpace (lowerBlockUnipotent h F.Carrier) := ⟨rfl⟩

/-- The actual lower first-block average with its positive slice density. -/
def firstBlockReflectedQuotientAverage
    (νA : Measure (LeftUnipotentQuotient (m 0) F.Carrier))
    (hInv : NormOneRightInvariant F (m 0) νA) (d : ℤ) :
    LowerMixedQuotient F h → ℂ :=
  fun q => (firstBlockReflectionDensity F (m := m) d : ℂ) *
    TwoBlockLowerFirstBlockQuotient.firstBlockAverage F h νA hInv d
      (TwoBlockDominantRectangular.quotientKernel ν ell f Wtest rfl 0) q

/-- The exact lower slice tower transfers actual lower convergence to the
small quotient fibers and identifies the integrated reflected average. -/
theorem firstBlockReflectedQuotientAverage_analysis
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (t + (j + k + 1) + 1) F.Carrier) V)
    (hπ : IsSmooth π) (hσ : IsSmooth (σ 0))
    (lambda : glFunctionals ψ (t + (j + k + 1)) π)
    (Wmodel : (coefficientModel π lambda).toSubmodule)
    (νA : Measure (LeftUnipotentQuotient (m 0) F.Carrier)) [SigmaFinite νA]
    (νL : Measure (LowerMixedQuotient F h))
    (νMinus : Measure (LowerQuotient h F.Carrier))
    (hνA : IsCompatible (upperUnipotent (m 0 + 1) F.Carrier)
      (generalLinearHaar F.Carrier (m 0)) (unipotentHaar F.Carrier (m 0)) νA)
    (hνL : IsCompatible (lowerMixedSubgroup F h) (generalLinearHaar F.Carrier t)
      (lowerMixedHaar F h) νL)
    (hνMinus : IsCompatible (lowerBlockUnipotent h F.Carrier) (generalLinearHaar F.Carrier t)
      (lowerHaar F h) νMinus) (d : ℤ)
    (hK : Integrable (TwoBlockDominantRectangular.quotientKernel ν ell f Wmodel.val rfl 0)
      (νMinus.restrict (TwoBlockLowerUnipotentQuotient.determinantSlice F h d)))
    (hN : Integrable (TwoBlockDominantRectangular.quotientNormProfile ν ell f Wmodel.val rfl 0)
      (νMinus.restrict (TwoBlockLowerUnipotentQuotient.determinantSlice F h d)))
    (hrect : ∀ᵐ z ∂νMinus.restrict (TwoBlockLowerUnipotentQuotient.determinantSlice F h d),
      TwoBlockDominantRectangular.quotientFiberIntegrable ν ell f Wmodel.val rfl 0 z) :
    let hInv := normOneRightInvariant_of_isCompatible F (m 0)
      (generalLinearHaar F.Carrier (m 0)) (unipotentHaar F.Carrier (m 0)) νA hνA
    let Q := firstBlockReflectedQuotientAverage F h j k ell f Wmodel.val ν νA hInv d
    let μL := νL.restrict (TwoBlockLowerFirstBlockQuotient.determinantSlice F h 0)
    Measurable Q ∧ Integrable Q μL ∧
    (∀ᵐ qbase ∂μL, ∀ g : GeneralLinear (t + 1) F.Carrier, qbase = Quotient.mk _ g →
      Integrable (fun Y => firstBlockReflectedSmallCoefficient F h j k ell f Wmodel.val ν νA d Y g)
        (rectangularMeasure ν j (m 1 + 1)) ∧
      Q qbase = ∫ Y, firstBlockReflectedSmallCoefficient F h j k ell f Wmodel.val ν νA d Y g
        ∂rectangularMeasure ν j (m 1 + 1)) ∧
    (∫ q, Q q ∂μL) = ∫ z, TwoBlockDominantRectangular.quotientKernel ν ell f Wmodel.val rfl 0 z
      ∂νMinus.restrict (TwoBlockLowerUnipotentQuotient.determinantSlice F h d) := by
  dsimp only
  let hInv := normOneRightInvariant_of_isCompatible F (m 0)
    (generalLinearHaar F.Carrier (m 0)) (unipotentHaar F.Carrier (m 0)) νA hνA
  let κ := firstBlockKernel F h νA hInv d
  let μL := νL.restrict (TwoBlockLowerFirstBlockQuotient.determinantSlice F h 0)
  let μA := νA.restrict (RankinSelberg.determinantSlice F.canonicalTopologicalData (m 0) d)
  let rho := firstBlockReflectionDensity F (m := m) d
  let K := TwoBlockDominantRectangular.quotientKernel ν ell f Wmodel.val rfl 0
  let N := TwoBlockDominantRectangular.quotientNormProfile ν ell f Wmodel.val rfl 0
  let : νA.Regular := hνA.regular
  let : IsSFiniteKernel κ := firstBlockKernel_isSFinite F h νA hInv d
  have hd := firstBlockDensity F (m 0) (m 1 + 1) d
  have hc : ENNReal.ofReal rho • (κ ∘ₘ μL) =
      νMinus.restrict (TwoBlockLowerUnipotentQuotient.determinantSlice F h d) :=
    firstBlockKernel_comp_zeroSlice F h νA hInv hνA νL hνL νMinus hνMinus d
  have hKm : Measurable K :=
    TwoBlockDominantRectangular.measurable_quotientKernel ν ell f π hπ lambda Wmodel rfl 0
  have hNm : Measurable N :=
    TwoBlockDominantRectangular.measurable_quotientNormProfile ν ell f π hπ lambda Wmodel rfl 0
  have hKc : Integrable K (κ ∘ₘ μL) := by
    apply (integrable_smul_measure hd.1.ne' hd.2.1.ne).mp
    change Integrable K (ENNReal.ofReal rho • (κ ∘ₘ μL))
    rwa [hc]
  have hNc : Integrable N (κ ∘ₘ μL) := by
    apply (integrable_smul_measure hd.1.ne' hd.2.1.ne).mp
    change Integrable N (ENNReal.ofReal rho • (κ ∘ₘ μL))
    rwa [hc]
  have hNae := ((Measure.integrable_comp_iff hNm.aestronglyMeasurable).mp hNc).1
  have hrectc : ∀ᵐ z ∂(κ ∘ₘ μL),
      TwoBlockDominantRectangular.quotientFiberIntegrable ν ell f Wmodel.val rfl 0 z := by
    apply (Measure.ae_ennreal_smul_measure_iff (show ENNReal.ofReal rho ≠ 0 from hd.1.ne')).mp
    rwa [hc]
  have hrectae := Measure.ae_ae_of_ae_comp hrectc
  let B := TwoBlockLowerFirstBlockQuotient.firstBlockAverage F h νA hInv d K
  have hB : B = fun q => ∫ z, K z ∂κ q :=
    firstBlockAverage_eq_integral_firstBlockKernel F h νA hInv d K hKm
  have hBm : Measurable B := by
    rw [hB]
    exact (hKm.stronglyMeasurable.integral_kernel (κ := κ)).measurable
  have hBi : Integrable B μL := by
    rw [hB]
    rw [Measure.comp_eq_comp_const_apply] at hKc
    exact hKc.integral_comp
  refine ⟨hBm.const_mul (rho : ℂ), hBi.const_mul (rho : ℂ), ?_, ?_⟩
  · filter_upwards [hNae, hrectae] with qbase hNq hRq g hqg
    subst qbase
    have hfm : Measurable (fun q => firstBlockFiberPoint F h q g) :=
      ((continuous_firstBlockFiberPoint F h).comp (continuous_id.prodMk continuous_const)).measurable
    rw [firstBlockKernel_mk] at hNq hRq
    have hNpull := hNq.comp_measurable hfm
    have hRpull := ae_of_ae_map hfm.aemeasurable hRq
    have hresult := firstBlockReflectedRowAverage_product_control F h j k ell f Wmodel.val ν
      (glModelFunction_continuous ψ _ π hπ lambda Wmodel) hσ νA hνA hInv d g hRpull hNpull
    exact ⟨hresult.2.1, hresult.2.2.symm⟩
  · change (∫ q, (rho : ℂ) * B q ∂μL) = _
    rw [integral_const_mul]
    symm
    rw [← hc, integral_smul_measure, Measure.comp_eq_comp_const_apply,
      Kernel.integral_comp (by simpa only [Measure.comp_eq_comp_const_apply] using hKc)]
    rw [← hB]
    simp only [Complex.real_smul]
    change ((ENNReal.ofReal rho).toReal : ℂ) * (∫ q, B q ∂μL) = _
    rw [ENNReal.toReal_ofReal (show 0 ≤ rho from
      firstBlockReflectionDensity_nonneg F (m := m) d)]

end Langlands.RankinSelberg.TwoBlockDominantFirstBlock
