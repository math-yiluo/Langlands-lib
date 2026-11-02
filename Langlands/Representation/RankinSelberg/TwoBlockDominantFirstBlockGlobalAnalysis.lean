import Langlands.Representation.RankinSelberg.TwoBlockDominantFirstBlockRowAnalysis
import Langlands.Representation.RankinSelberg.TwoBlockLowerFirstBlockRadicalAnalysis

/-! # Global convergence for the upper first-block disintegration -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.RankinSelberg.TwoBlockDominantFirstBlock

open MeasureTheory ProbabilityTheory GeneralLinear Whittaker HarmonicAnalysis TwoBlockJacquet
  TwoBlockFirstBlockQuotient TwoBlockLowerFirstBlockQuotient TwoBlockFirstBlockLaurent
  QuotientIntegration TwoBlockLowerUnipotentQuotient
open scoped ENNReal

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance globalAnalysisTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance globalAnalysisValuation : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance globalAnalysisLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance globalAnalysisT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance globalAnalysisCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance globalAnalysisGLTopology (a : ℕ) : IsTopologicalGroup (GeneralLinear a F.Carrier) :=
  F.canonicalTopologicalData.generalLinearTopologicalGroup a
local instance globalAnalysisGLCountable (a : ℕ) : SecondCountableTopology (GeneralLinear a F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology a
local instance globalAnalysisMeasurable : MeasurableSpace F.Carrier := borel _
local instance globalAnalysisBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance globalAnalysisGLMeasurable (a : ℕ) : MeasurableSpace (GeneralLinear a F.Carrier) := borel _
local instance globalAnalysisGLBorel (a : ℕ) : BorelSpace (GeneralLinear a F.Carrier) := ⟨rfl⟩
local instance globalAnalysisNMeasurable (a : ℕ) :
    MeasurableSpace (upperUnipotent a F.Carrier) := borel _
local instance globalAnalysisNBorel (a : ℕ) : BorelSpace (upperUnipotent a F.Carrier) := ⟨rfl⟩
local instance globalAnalysisNCountable (a : ℕ) :
    SecondCountableTopology (upperUnipotent a F.Carrier) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance globalAnalysisNQMeasurable (a : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient a F.Carrier) := borel _
local instance globalAnalysisNQBorel (a : ℕ) :
    BorelSpace (LeftUnipotentQuotient a F.Carrier) := ⟨rfl⟩

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1) (j k : ℕ)
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
variable {σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i)}
variable {ψ : UnitaryAdditiveCharacter F.Carrier}
variable (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i)) (f : Sections F h σ)
variable (Wtest : WhittakerFunctions ψ (t + (j + k + 1)))
variable (ν : AdditiveHaarMeasure F.Carrier)

/-- The upper first-block coefficient integrated over the remaining external
second-block columns, with the actual supplied quotient and rectangle measures. -/
def firstBlockUpperGlobalAverage
    (μ : Measure (LeftUnipotentQuotient (m 0) F.Carrier)) (d : ℤ)
    (g : GeneralLinear (t + 1) F.Carrier) : ℂ :=
  ∫ Y, firstBlockUpperCoefficient F h j k ell f Wtest ν μ d Y g
    ∂rectangularMeasure ν j (m 1 + 1)

local instance globalAnalysisHQMeasurable :
    MeasurableSpace (TwoBlockUnipotentQuotient.BlockQuotient h F.Carrier) := borel _
local instance globalAnalysisHQBorel :
    BorelSpace (TwoBlockUnipotentQuotient.BlockQuotient h F.Carrier) := ⟨rfl⟩
local instance globalAnalysisHMeasurable :
    MeasurableSpace (TwoBlockUnipotentQuotient.blockUnipotent h F.Carrier) := borel _
local instance globalAnalysisHBorel :
    BorelSpace (TwoBlockUnipotentQuotient.blockUnipotent h F.Carrier) := ⟨rfl⟩
local instance globalAnalysisMixedSubgroupMeasurable :
    MeasurableSpace (mixedSubgroup F h) := borel _
local instance globalAnalysisMixedSubgroupBorel : BorelSpace (mixedSubgroup F h) := ⟨rfl⟩
local instance globalAnalysisLowerMixedSubgroupMeasurable :
    MeasurableSpace (lowerMixedSubgroup F h) := borel _
local instance globalAnalysisLowerMixedSubgroupBorel : BorelSpace (lowerMixedSubgroup F h) := ⟨rfl⟩
local instance globalAnalysisMixedMeasurable :
    MeasurableSpace (MixedQuotient F h) := borel _
local instance globalAnalysisMixedBorel : BorelSpace (MixedQuotient F h) := ⟨rfl⟩
local instance globalAnalysisLowerMixedMeasurable :
    MeasurableSpace (LowerMixedQuotient F h) := borel _
local instance globalAnalysisLowerMixedBorel : BorelSpace (LowerMixedQuotient F h) := ⟨rfl⟩

/-- Joint measurability retains the radical, small quotient and remaining
external columns. No measurable quotient representative is chosen. -/
theorem firstBlockUpperRowAverage_joint_stronglyMeasurable
    (hW : Continuous Wtest.val) (hσ : IsSmooth (σ 0)) (s : ℂ)
    (g : GeneralLinear (t + 1) F.Carrier) :
    StronglyMeasurable (fun z :
        (Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier ×
          LeftUnipotentQuotient (m 0) F.Carrier) ×
            Matrix (Fin j) (Fin (m 1 + 1)) F.Carrier =>
      firstBlockUpperRowAverage F h j k ell f Wtest ν s z.1.2 z.1.1 z.2 g) := by
  have := TwoBlockLowerUnfolding.sigmaFinite_additiveHaarMeasure ν
  have hsmall : Continuous (firstBlockCoefficient ell f g).val.val := by
    obtain ⟨v, hv⟩ := modelMap_surjective (σ 0) (ell 0) (firstBlockCoefficient ell f g)
    rw [← hv]
    exact (matrixCoefficient_isLocallyConstant (σ 0) (ell 0).val v (hσ v)).continuous
  have hi := (continuous_translated_unequalRankIntegrandAt F (m 1 + 1 + j) k
    (firstBlockSmallRank h j k) ψ Wtest (firstBlockCoefficient ell f g).val
    hW hsmall s).measurable.stronglyMeasurable
  have hcols : Measurable (fun Y : Matrix (Fin j) (Fin (m 1 + 1)) F.Carrier =>
      firstBlockColumns h j (0 : Matrix (Fin j) (Fin (m 0 + 1)) F.Carrier) Y) := by
    simpa only [Function.comp_def, id_eq, firstBlockColumnJoinEquiv_apply] using
      (firstBlockColumnJoinEquiv F.Carrier h j).measurable.comp
        ((measurable_const (a := (0 : Matrix (Fin j) (Fin (m 0 + 1)) F.Carrier))).prodMk
          measurable_id)
  have htrans : Measurable (fun Y : Matrix (Fin j) (Fin (m 1 + 1)) F.Carrier =>
      rectangularUnipotent j k (firstBlockColumns h j 0 Y) *
        appendIdentity t (j + k + 1) g) :=
    ((continuous_rectangularUnipotent j k).measurable.comp hcols).mul_const _
  have hrows : Measurable (fun z :
        Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier ×
          Matrix (Fin j) (Fin (m 0 + 1)) F.Carrier =>
      firstBlockRows j z.1 z.2) := by
    simpa only [Function.comp_def, id_eq, firstBlockRowJoinEquiv_apply, firstBlockRows] using
      (firstBlockRowJoinEquiv F.Carrier (m 0 + 1) (m 1 + 1) j).measurable.comp
        (measurable_fst.prodMk measurable_snd)
  have hm := hi.comp_measurable
    (measurable_fst.fst.snd.prodMk
      ((hrows.comp (measurable_fst.fst.fst.prodMk measurable_snd)).prodMk
        (htrans.comp measurable_fst.snd)))
  have ha := hm.integral_prod_right' (ν := rectangularMeasure ν j (m 0 + 1))
  simpa only [firstBlockUpperRowAverage_eq, Function.comp_def] using
    ha.const_mul (determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) g
      (s - ((j + k + 1 : ℕ) : ℂ) / 2 + (j : ℂ)))

/-- The original raw norm on the actual radical/quotient product controls the
three-variable row average and justifies moving the remaining columns outside. -/
theorem firstBlockUpperRowAverage_joint_product_control
    (hW : Continuous Wtest.val) (hσ : IsSmooth (σ 0)) (s : ℂ)
    (μZ : Measure (Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier)) [SFinite μZ]
    (μ : Measure (LeftUnipotentQuotient (m 0) F.Carrier)) [SFinite μ]
    (g : GeneralLinear (t + 1) F.Carrier)
    (hrect : ∀ᵐ z ∂μZ.prod μ, Integrable
      (fun x => rectangularSectionIntegrand F ell f j k Wtest
        (quotientDeterminantWeight F t (s - ((j + k + 1 : ℕ) : ℂ) / 2)) x
        (fiberPoint h F.Carrier z.2 (lowerRadical h F.Carrier z.1 * g)))
      (rectangularMeasure ν j (t + 1)))
    (hN : Integrable (fun z =>
      rectangularSectionNormProfile F ell f j k Wtest ν
        (quotientDeterminantWeight F t (s - ((j + k + 1 : ℕ) : ℂ) / 2))
        (fiberPoint h F.Carrier z.2 (lowerRadical h F.Carrier z.1 * g))) (μZ.prod μ)) :
    Integrable (fun z :
        (Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier ×
          LeftUnipotentQuotient (m 0) F.Carrier) ×
            Matrix (Fin j) (Fin (m 1 + 1)) F.Carrier =>
      firstBlockUpperRowAverage F h j k ell f Wtest ν s z.1.2 z.1.1 z.2 g)
      ((μZ.prod μ).prod (rectangularMeasure ν j (m 1 + 1))) ∧
    (∫ Z, ∫ q, rectangularSectionAverage F ell f j k Wtest ν
      (quotientDeterminantWeight F t (s - ((j + k + 1 : ℕ) : ℂ) / 2))
      (fiberPoint h F.Carrier q (lowerRadical h F.Carrier Z * g)) ∂μ ∂μZ) =
      ∫ Y, ∫ Z, ∫ q, firstBlockUpperRowAverage F h j k ell f Wtest ν s q Z Y g
        ∂μ ∂μZ ∂rectangularMeasure ν j (m 1 + 1) := by
  have := TwoBlockLowerUnfolding.sigmaFinite_additiveHaarMeasure ν
  have hm := firstBlockUpperRowAverage_joint_stronglyMeasurable
    F h j k ell f Wtest ν hW hσ s g
  have hp : Integrable (fun z =>
      firstBlockUpperColumnNormProfile F h j k ell f Wtest ν s z.2 z.1 g)
      (μZ.prod μ) := by
    apply hN.mono' hm.norm.integral_prod_right'.aestronglyMeasurable
    filter_upwards [hrect] with z hz
    have hn : 0 ≤ firstBlockUpperColumnNormProfile F h j k ell f Wtest ν s z.2 z.1 g :=
      integral_nonneg (fun _ => norm_nonneg _)
    change ‖firstBlockUpperColumnNormProfile F h j k ell f Wtest ν s z.2 z.1 g‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg hn]
    exact (firstBlockUpperRowAverage_column_control
      F h j k ell f Wtest ν s z.2 z.1 g hz).2.1
  have hi : Integrable (fun z :
        (Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier ×
          LeftUnipotentQuotient (m 0) F.Carrier) ×
            Matrix (Fin j) (Fin (m 1 + 1)) F.Carrier =>
      firstBlockUpperRowAverage F h j k ell f Wtest ν s z.1.2 z.1.1 z.2 g)
      ((μZ.prod μ).prod (rectangularMeasure ν j (m 1 + 1))) := by
    apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
    refine ⟨?_, hp⟩
    filter_upwards [hrect] with z hz
    exact (firstBlockUpperRowAverage_column_control
      F h j k ell f Wtest ν s z.2 z.1 g hz).1
  have he := Measure.ae_ae_of_ae_prod hrect
  refine ⟨hi, ?_⟩
  calc
    _ = ∫ Z, ∫ q, ∫ Y,
        firstBlockUpperRowAverage F h j k ell f Wtest ν s q Z Y g
          ∂rectangularMeasure ν j (m 1 + 1) ∂μ ∂μZ := by
      apply integral_congr_ae
      filter_upwards [he] with Z hZ
      apply integral_congr_ae
      filter_upwards [hZ] with q hq
      exact (firstBlockUpperRowAverage_column_control
        F h j k ell f Wtest ν s q Z g hq).2.2.symm
    _ = ∫ z, ∫ Y,
        firstBlockUpperRowAverage F h j k ell f Wtest ν s z.2 z.1 Y g
          ∂rectangularMeasure ν j (m 1 + 1) ∂μZ.prod μ :=
      (integral_prod _ hi.integral_prod_left).symm
    _ = ∫ Y, ∫ z,
        firstBlockUpperRowAverage F h j k ell f Wtest ν s z.2 z.1 Y g
          ∂μZ.prod μ ∂rectangularMeasure ν j (m 1 + 1) :=
      integral_integral_swap hi
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [hi.prod_left_ae] with Y hY
      exact integral_prod _ hY

/-- Composing the exact first-block and radical towers gives genuine
integrability on the actual radical/small-quotient product almost everywhere
on the lower mixed zero slice. This applies to any measurable raw profile. -/
theorem integrable_firstBlock_radical_product_ae
    (N : TwoBlockUnipotentQuotient.BlockQuotient h F.Carrier → ℝ) (hNm : Measurable N)
    (μZ : Measure (Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier))
    [μZ.IsAddHaarMeasure] [SFinite μZ]
    (νH : Measure (TwoBlockUnipotentQuotient.BlockQuotient h F.Carrier))
    (νA : Measure (LeftUnipotentQuotient (m 0) F.Carrier)) [SigmaFinite νA]
    (νM : Measure (MixedQuotient F h)) (νL : Measure (LowerMixedQuotient F h))
    (hνH : IsCompatible (TwoBlockUnipotentQuotient.blockUnipotent h F.Carrier)
      (generalLinearHaar F.Carrier t) (TwoBlockUnipotentQuotient.blockHaar F.Carrier h) νH)
    (hνA : IsCompatible (upperUnipotent (m 0 + 1) F.Carrier)
      (generalLinearHaar F.Carrier (m 0)) (unipotentHaar F.Carrier (m 0)) νA)
    (hνM : IsCompatible (mixedSubgroup F h) (generalLinearHaar F.Carrier t)
      (mixedHaar F h) νM)
    (hνL : IsCompatible (lowerMixedSubgroup F h) (generalLinearHaar F.Carrier t)
      (lowerMixedHaar F h) νL)
    (d : ℤ)
    (hNi : Integrable N
      (νH.restrict (TwoBlockUnipotentQuotient.determinantSlice F h d))) :
    ∀ᵐ qbase ∂νL.restrict (TwoBlockLowerFirstBlockQuotient.determinantSlice F h 0),
      ∀ g : GeneralLinear (t + 1) F.Carrier, qbase = Quotient.mk _ g →
        Integrable (fun z :
            Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier ×
              LeftUnipotentQuotient (m 0) F.Carrier =>
          N (fiberPoint h F.Carrier z.2 (lowerRadical h F.Carrier z.1 * g)))
          (μZ.prod (νA.restrict
            (RankinSelberg.determinantSlice F.canonicalTopologicalData (m 0) d))) := by
  let hInv := normOneRightInvariant_of_isCompatible F (m 0)
    (generalLinearHaar F.Carrier (m 0)) (unipotentHaar F.Carrier (m 0)) νA hνA
  let κA := fiberKernel F h νA hInv d
  let κR := radicalKernel F h μZ
  let μL := νL.restrict (TwoBlockLowerFirstBlockQuotient.determinantSlice F h 0)
  let μA := νA.restrict (RankinSelberg.determinantSlice F.canonicalTopologicalData (m 0) d)
  let c := μZ {Z | ∀ i j, Z i j ∈ Valuation.integer (ValuativeRel.valuation F.Carrier)}
  have hzero := (normalized_tower F h νA hInv hνA νM hνM νH hνH).2
  have hcompA := fiberKernel_comp_zeroSlice_eq F h νA hInv hνA νM hνM νH hzero d
  have hcompR := (radicalTower F h μZ νL hνL νM hνM).2 0
  have hcomp : (κA ∘ₖ κR) ∘ₘ μL =
      c • νH.restrict (TwoBlockUnipotentQuotient.determinantSlice F h d) := by
    rw [← Measure.comp_assoc, hcompR, Measure.comp_smul, hcompA]
  have hc := TwoBlockUnipotentQuotient.integerCube_mass_pos_lt_top F
    (m 1 + 1) (m 0 + 1) μZ
  have hNc : Integrable N ((κA ∘ₖ κR) ∘ₘ μL) := by
    rw [hcomp]
    exact hNi.smul_measure hc.2.ne
  have hNae := ((Measure.integrable_comp_iff hNm.aestronglyMeasurable).mp hNc).1
  filter_upwards [hNae] with qbase hq g hqg
  subst qbase
  have hfmR : Measurable (fun Z => radicalFiberPoint F h Z g) :=
    ((continuous_radicalFiberPoint F h).comp (continuous_id.prodMk continuous_const)).measurable
  have hNcR : Integrable N (κA ∘ₘ κR (Quotient.mk _ g)) := by
    simpa only [Kernel.comp_apply] using hq
  obtain ⟨hNfiber, hNnorm⟩ :=
    (Measure.integrable_comp_iff hNm.aestronglyMeasurable).mp hNcR
  rw [radicalKernel_mk] at hNfiber hNnorm
  have hNfiberZ := ae_of_ae_map hfmR.aemeasurable hNfiber
  have hNnormZ := hNnorm.comp_measurable hfmR
  have hfmA (Z : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier) :
      Measurable (fun q : LeftUnipotentQuotient (m 0) F.Carrier =>
        fiberPoint h F.Carrier q (lowerRadical h F.Carrier Z * g)) :=
    ((continuous_fiberPoint F h).comp (continuous_id.prodMk continuous_const)).measurable
  have hfm : Measurable (fun z :
        Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier ×
          LeftUnipotentQuotient (m 0) F.Carrier =>
      fiberPoint h F.Carrier z.2 (lowerRadical h F.Carrier z.1 * g)) :=
    (continuous_fiberPoint F h).measurable.comp
      (measurable_snd.prodMk
        (((continuous_lowerRadical h F.Carrier).measurable.comp measurable_fst).mul_const g))
  apply (integrable_prod_iff (hNm.comp hfm).aestronglyMeasurable).mpr
  constructor
  · filter_upwards [hNfiberZ] with Z hZ
    rw [radicalFiberPoint_def, fiberKernel_mk] at hZ
    exact hZ.comp_measurable (hfmA Z)
  · convert hNnormZ using 1
    funext Z
    dsimp only [Function.comp_def]
    rw [radicalFiberPoint_def, fiberKernel_mk]
    exact (integral_map (hfmA Z).aemeasurable hNm.norm.aestronglyMeasurable).symm

end Langlands.RankinSelberg.TwoBlockDominantFirstBlock
