import Langlands.Representation.RankinSelberg.TwoBlockDominantFirstBlockRectangleChange

/-! # Measurable row averages and the original raw-norm majorant -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.RankinSelberg.TwoBlockDominantFirstBlock

open MeasureTheory GeneralLinear Whittaker HarmonicAnalysis TwoBlockJacquet
  TwoBlockFirstBlockQuotient TwoBlockLowerFirstBlockQuotient TwoBlockFirstBlockLaurent
  QuotientIntegration TwoBlockLowerUnipotentQuotient

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance rowAnalysisTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance rowAnalysisValuation : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance rowAnalysisLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance rowAnalysisCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance rowAnalysisGLTopology (a : ℕ) : IsTopologicalGroup (GeneralLinear a F.Carrier) :=
  F.canonicalTopologicalData.generalLinearTopologicalGroup a
local instance rowAnalysisGLCountable (a : ℕ) : SecondCountableTopology (GeneralLinear a F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology a
local instance rowAnalysisMeasurable : MeasurableSpace F.Carrier := borel _
local instance rowAnalysisBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance rowAnalysisGLMeasurable (a : ℕ) : MeasurableSpace (GeneralLinear a F.Carrier) := borel _
local instance rowAnalysisGLBorel (a : ℕ) : BorelSpace (GeneralLinear a F.Carrier) := ⟨rfl⟩
local instance rowAnalysisNQMeasurable (a : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient a F.Carrier) := borel _
local instance rowAnalysisNQBorel (a : ℕ) :
    BorelSpace (LeftUnipotentQuotient a F.Carrier) := ⟨rfl⟩

private theorem rowAnalysis_continuous_appendIdentity (n d : ℕ) :
    Continuous (appendIdentity (F := F.Carrier) n d) := by
  induction d with
  | zero => exact continuous_id
  | succ d ih => exact (rankInclusionContinuous 1).continuous.comp ih

/-- Joint continuity on the actual quotient, with the rectangular and
right-translation parameters both retained. -/
theorem continuous_translated_unequalRankIntegrandAt {n r : ℕ} (j k : ℕ)
    (hr : r = n + (j + k + 1)) (ψ : UnitaryAdditiveCharacter F.Carrier)
    (Wtest : WhittakerFunctions ψ r) (Wsmall : InverseWhittakerFunctions ψ n)
    (hW : Continuous Wtest.val) (hWsmall : Continuous Wsmall.val) (s : ℂ) :
    Continuous (fun z : LeftUnipotentQuotient n F.Carrier ×
        (Matrix (Fin j) (Fin (n + 1)) F.Carrier × GeneralLinear (r + 1) F.Carrier) =>
      unequalRankIntegrandAt F j k hr ψ (normalizedAbsoluteValue F.canonicalTopologicalData)
        (translateWhittaker ψ r Wtest z.2.2) Wsmall s z.2.1 z.1) := by
  subst r
  apply ((leftQuotient_isOpenQuotientMap (upperUnipotent (n + 1) F.Carrier)).prodMap
    IsOpenQuotientMap.id).isQuotientMap.continuous_iff.mpr
  change Continuous (fun z : GeneralLinear (n + 1) F.Carrier ×
      (Matrix (Fin j) (Fin (n + 1)) F.Carrier ×
        GeneralLinear (n + (j + k + 1) + 1) F.Carrier) =>
    Wtest.val (unequalRankMatrix j k z.1 z.2.1 * z.2.2) *
      Wsmall.val z.1 *
      determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) z.1
        (s - ((j + k + 1 : ℕ) : ℂ) / 2))
  have hm : Continuous (fun z : GeneralLinear (n + 1) F.Carrier ×
      (Matrix (Fin j) (Fin (n + 1)) F.Carrier ×
        GeneralLinear (n + (j + k + 1) + 1) F.Carrier) =>
      unequalRankMatrix j k z.1 z.2.1) :=
    ((rowAnalysis_continuous_appendIdentity F n (j + k + 1)).comp continuous_fst).mul
      ((continuous_rectangularUnipotent j k).comp continuous_snd.fst)
  have hd : Continuous (fun v : GeneralLinear (n + 1) F.Carrier =>
      determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) v
        (s - ((j + k + 1 : ℕ) : ℂ) / 2)) :=
    (quotientDeterminantWeight_continuous F n _).comp continuous_quotient_mk'
  exact ((hW.comp (hm.mul continuous_snd.snd)).mul
    (hWsmall.comp continuous_fst)).mul (hd.comp continuous_fst)

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1) (j k : ℕ)
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
variable {σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i)}
variable {ψ : UnitaryAdditiveCharacter F.Carrier}
variable (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i)) (f : Sections F h σ)
variable (Wtest : WhittakerFunctions ψ (t + (j + k + 1)))
variable (ν : AdditiveHaarMeasure F.Carrier)

local instance rowAnalysisHQMeasurable :
    MeasurableSpace (TwoBlockUnipotentQuotient.BlockQuotient h F.Carrier) := borel _
local instance rowAnalysisHQBorel :
    BorelSpace (TwoBlockUnipotentQuotient.BlockQuotient h F.Carrier) := ⟨rfl⟩

/-- Integrate the norm after averaging the external first-block rows. -/
def firstBlockUpperColumnNormProfile (s : ℂ)
    (q : LeftUnipotentQuotient (m 0) F.Carrier)
    (Z : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier)
    (g : GeneralLinear (t + 1) F.Carrier) : ℝ :=
  ∫ Y, ‖firstBlockUpperRowAverage F h j k ell f Wtest ν s q Z Y g‖
    ∂rectangularMeasure ν j (m 1 + 1)

/-- Measurability comes from the actual smaller integrand, without a
measurable choice of quotient representatives. -/
theorem firstBlockUpperRowAverage_stronglyMeasurable
    (hW : Continuous Wtest.val) (hσ : IsSmooth (σ 0)) (s : ℂ)
    (Z : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier)
    (g : GeneralLinear (t + 1) F.Carrier) :
    StronglyMeasurable (fun z : LeftUnipotentQuotient (m 0) F.Carrier ×
        Matrix (Fin j) (Fin (m 1 + 1)) F.Carrier =>
      firstBlockUpperRowAverage F h j k ell f Wtest ν s z.1 Z z.2 g) := by
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
  have hrows : Measurable (fun T : Matrix (Fin j) (Fin (m 0 + 1)) F.Carrier =>
      firstBlockRows j Z T) := by
    simpa only [Function.comp_def, id_eq, firstBlockRowJoinEquiv_apply, firstBlockRows] using
      (firstBlockRowJoinEquiv F.Carrier (m 0 + 1) (m 1 + 1) j).measurable.comp
        ((measurable_const (a := Z)).prodMk measurable_id)
  have hm := hi.comp_measurable
    (measurable_fst.fst.prodMk
      ((hrows.comp measurable_snd).prodMk (htrans.comp measurable_fst.snd)))
  have ha := hm.integral_prod_right' (ν := rectangularMeasure ν j (m 0 + 1))
  simpa only [firstBlockUpperRowAverage_eq, Function.comp_def] using
    ha.const_mul (determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) g
      (s - ((j + k + 1 : ℕ) : ℂ) / 2 + (j : ℂ)))

/-- The column norm profile is measurable on the actual small quotient. -/
theorem firstBlockUpperColumnNormProfile_measurable
    (hW : Continuous Wtest.val) (hσ : IsSmooth (σ 0)) (s : ℂ)
    (Z : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier)
    (g : GeneralLinear (t + 1) F.Carrier) :
    Measurable (fun q => firstBlockUpperColumnNormProfile F h j k ell f Wtest ν s q Z g) := by
  exact (firstBlockUpperRowAverage_stronglyMeasurable F h j k ell f Wtest ν
    hW hσ s Z g).norm.integral_prod_right'.measurable

/-- At each original rectangle fiber, the row average is integrable in the
remaining columns, its real norm integral is bounded by the original raw norm,
and its signed integral is the original rectangle average. -/
theorem firstBlockUpperRowAverage_column_control (s : ℂ)
    (q : LeftUnipotentQuotient (m 0) F.Carrier)
    (Z : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier)
    (g : GeneralLinear (t + 1) F.Carrier)
    (hi : Integrable (fun x => rectangularSectionIntegrand F ell f j k Wtest
      (quotientDeterminantWeight F t (s - ((j + k + 1 : ℕ) : ℂ) / 2)) x
      (fiberPoint h F.Carrier q (lowerRadical h F.Carrier Z * g)))
        (rectangularMeasure ν j (t + 1))) :
    Integrable (fun Y => firstBlockUpperRowAverage F h j k ell f Wtest ν s q Z Y g)
      (rectangularMeasure ν j (m 1 + 1)) ∧
    firstBlockUpperColumnNormProfile F h j k ell f Wtest ν s q Z g ≤
      rectangularSectionNormProfile F ell f j k Wtest ν
        (quotientDeterminantWeight F t (s - ((j + k + 1 : ℕ) : ℂ) / 2))
        (fiberPoint h F.Carrier q (lowerRadical h F.Carrier Z * g)) ∧
    (∫ Y, firstBlockUpperRowAverage F h j k ell f Wtest ν s q Z Y g
      ∂rectangularMeasure ν j (m 1 + 1)) =
      rectangularSectionAverage F ell f j k Wtest ν
        (quotientDeterminantWeight F t (s - ((j + k + 1 : ℕ) : ℂ) / 2))
        (fiberPoint h F.Carrier q (lowerRadical h F.Carrier Z * g)) := by
  have := TwoBlockLowerUnfolding.sigmaFinite_additiveHaarMeasure ν
  let G := firstBlockEmbedding h F.Carrier q.out * (lowerRadical h F.Carrier Z * g)
  have hpoint : fiberPoint h F.Carrier q (lowerRadical h F.Carrier Z * g) =
      Quotient.mk _ G := by
    simpa only [Quotient.out_eq] using
      fiberPoint_mk h F.Carrier q.out (lowerRadical h F.Carrier Z * g)
  rw [hpoint] at hi ⊢
  have hu := (integrable_firstBlockUpperValue_original_iff
    F h j k ell f Wtest ν s G).mpr hi
  have hc := (integrable_firstBlockColumns_iff F.Carrier h j ν _).mpr hu
  have ha : Integrable
      (fun Y => firstBlockUpperRowAverage F h j k ell f Wtest ν s q Z Y g)
      (rectangularMeasure ν j (m 1 + 1)) := hc.integral_prod_right
  refine ⟨ha, ?_, ?_⟩
  · calc
      _ ≤ ∫ Y, ∫ U, ‖firstBlockUpperValue F h j k ell f Wtest s G
          (firstBlockColumns h j U Y)‖
          ∂rectangularMeasure ν j (m 0 + 1)
          ∂rectangularMeasure ν j (m 1 + 1) :=
        integral_mono ha.norm hc.norm.integral_prod_right
          (fun Y => norm_integral_le_integral_norm _)
      _ = _ := integral_norm_firstBlockUpperValue_columns F h j k ell f Wtest ν s G hi
  · exact integral_firstBlockUpperValue_columns F h j k ell f Wtest ν s G hi

/-- Original raw-norm integrability supplies the actual quotient/column product
integrability and justifies interchanging those two integrals. -/
theorem firstBlockUpperRowAverage_product_control
    (hW : Continuous Wtest.val) (hσ : IsSmooth (σ 0)) (s : ℂ)
    (μ : Measure (LeftUnipotentQuotient (m 0) F.Carrier)) [SFinite μ]
    (Z : Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier)
    (g : GeneralLinear (t + 1) F.Carrier)
    (hrect : ∀ᵐ q ∂μ, Integrable
      (fun x => rectangularSectionIntegrand F ell f j k Wtest
        (quotientDeterminantWeight F t (s - ((j + k + 1 : ℕ) : ℂ) / 2)) x
        (fiberPoint h F.Carrier q (lowerRadical h F.Carrier Z * g)))
      (rectangularMeasure ν j (t + 1)))
    (hN : Integrable (fun q => rectangularSectionNormProfile F ell f j k Wtest ν
      (quotientDeterminantWeight F t (s - ((j + k + 1 : ℕ) : ℂ) / 2))
      (fiberPoint h F.Carrier q (lowerRadical h F.Carrier Z * g))) μ) :
    Integrable (fun z : LeftUnipotentQuotient (m 0) F.Carrier ×
        Matrix (Fin j) (Fin (m 1 + 1)) F.Carrier =>
      firstBlockUpperRowAverage F h j k ell f Wtest ν s z.1 Z z.2 g)
      (μ.prod (rectangularMeasure ν j (m 1 + 1))) ∧
    (∫ q, rectangularSectionAverage F ell f j k Wtest ν
      (quotientDeterminantWeight F t (s - ((j + k + 1 : ℕ) : ℂ) / 2))
      (fiberPoint h F.Carrier q (lowerRadical h F.Carrier Z * g)) ∂μ) =
      ∫ Y, ∫ q, firstBlockUpperRowAverage F h j k ell f Wtest ν s q Z Y g ∂μ
        ∂rectangularMeasure ν j (m 1 + 1) := by
  have := TwoBlockLowerUnfolding.sigmaFinite_additiveHaarMeasure ν
  have hm := firstBlockUpperRowAverage_stronglyMeasurable
    F h j k ell f Wtest ν hW hσ s Z g
  have hp : Integrable
      (fun q => firstBlockUpperColumnNormProfile F h j k ell f Wtest ν s q Z g) μ := by
    apply hN.mono' (firstBlockUpperColumnNormProfile_measurable
      F h j k ell f Wtest ν hW hσ s Z g).aestronglyMeasurable
    filter_upwards [hrect] with q hq
    have hn : 0 ≤ firstBlockUpperColumnNormProfile F h j k ell f Wtest ν s q Z g :=
      integral_nonneg (fun _ => norm_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg hn]
    exact (firstBlockUpperRowAverage_column_control F h j k ell f Wtest ν s q Z g hq).2.1
  have hi : Integrable (fun z : LeftUnipotentQuotient (m 0) F.Carrier ×
        Matrix (Fin j) (Fin (m 1 + 1)) F.Carrier =>
      firstBlockUpperRowAverage F h j k ell f Wtest ν s z.1 Z z.2 g)
      (μ.prod (rectangularMeasure ν j (m 1 + 1))) := by
    apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
    refine ⟨?_, hp⟩
    filter_upwards [hrect] with q hq
    exact (firstBlockUpperRowAverage_column_control F h j k ell f Wtest ν s q Z g hq).1
  refine ⟨hi, ?_⟩
  calc
    _ = ∫ q, ∫ Y, firstBlockUpperRowAverage F h j k ell f Wtest ν s q Z Y g
        ∂rectangularMeasure ν j (m 1 + 1) ∂μ := by
      apply integral_congr_ae
      filter_upwards [hrect] with q hq
      exact (firstBlockUpperRowAverage_column_control
        F h j k ell f Wtest ν s q Z g hq).2.2.symm
    _ = _ := integral_integral_swap hi

end Langlands.RankinSelberg.TwoBlockDominantFirstBlock
