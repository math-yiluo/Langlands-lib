import Langlands.Representation.RankinSelberg.TwoBlockDominantFirstBlockReflectionGlobal
import Langlands.Representation.RankinSelberg.TwoBlockLowerFirstBlockSliceAnalysis
import Langlands.Representation.RankinSelberg.TwoBlockDominantFirstBlockUpperUnfolding

/-! # Integrating the finite first-block Laurent identity -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.RankinSelberg.TwoBlockDominantFirstBlock

open MeasureTheory ProbabilityTheory GeneralLinear Whittaker HarmonicAnalysis TwoBlockJacquet
  TwoBlockFirstBlockQuotient TwoBlockLowerFirstBlockQuotient TwoBlockFirstBlockLaurent
  QuotientIntegration TwoBlockLowerUnipotentQuotient
open HarmonicAnalysis.BilateralLaurentSeries
open scoped ENNReal

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance globalLaurentTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance globalLaurentValuation : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance globalLaurentLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance globalLaurentT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance globalLaurentCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance globalLaurentGLTopology (a : ℕ) : IsTopologicalGroup (GeneralLinear a F.Carrier) :=
  F.canonicalTopologicalData.generalLinearTopologicalGroup a
local instance globalLaurentGLCountable (a : ℕ) : SecondCountableTopology (GeneralLinear a F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology a
local instance globalLaurentMeasurable : MeasurableSpace F.Carrier := borel _
local instance globalLaurentBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance globalLaurentGLMeasurable (a : ℕ) : MeasurableSpace (GeneralLinear a F.Carrier) := borel _
local instance globalLaurentGLBorel (a : ℕ) : BorelSpace (GeneralLinear a F.Carrier) := ⟨rfl⟩
local instance globalLaurentNMeasurable (a : ℕ) :
    MeasurableSpace (upperUnipotent a F.Carrier) := borel _
local instance globalLaurentNBorel (a : ℕ) : BorelSpace (upperUnipotent a F.Carrier) := ⟨rfl⟩
local instance globalLaurentNCountable (a : ℕ) :
    SecondCountableTopology (upperUnipotent a F.Carrier) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance globalLaurentNQMeasurable (a : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient a F.Carrier) := borel _
local instance globalLaurentNQBorel (a : ℕ) :
    BorelSpace (LeftUnipotentQuotient a F.Carrier) := ⟨rfl⟩

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1) (j k : ℕ)
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
variable {σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i)}
variable {ψ : UnitaryAdditiveCharacter F.Carrier}
variable (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i)) (f : Sections F h σ)
variable (Wtest : WhittakerFunctions ψ (t + (j + k + 1)))
variable (ν : AdditiveHaarMeasure F.Carrier)

local instance globalLaurentHQMeasurable :
    MeasurableSpace (TwoBlockUnipotentQuotient.BlockQuotient h F.Carrier) := borel _
local instance globalLaurentHQBorel :
    BorelSpace (TwoBlockUnipotentQuotient.BlockQuotient h F.Carrier) := ⟨rfl⟩
local instance globalLaurentHMeasurable :
    MeasurableSpace (TwoBlockUnipotentQuotient.blockUnipotent h F.Carrier) := borel _
local instance globalLaurentHBorel :
    BorelSpace (TwoBlockUnipotentQuotient.blockUnipotent h F.Carrier) := ⟨rfl⟩
local instance globalLaurentMixedSubgroupMeasurable :
    MeasurableSpace (mixedSubgroup F h) := borel _
local instance globalLaurentMixedSubgroupBorel : BorelSpace (mixedSubgroup F h) := ⟨rfl⟩
local instance globalLaurentLowerMixedSubgroupMeasurable :
    MeasurableSpace (lowerMixedSubgroup F h) := borel _
local instance globalLaurentLowerMixedSubgroupBorel : BorelSpace (lowerMixedSubgroup F h) := ⟨rfl⟩
local instance globalLaurentMixedMeasurable :
    MeasurableSpace (MixedQuotient F h) := borel _
local instance globalLaurentMixedBorel : BorelSpace (MixedQuotient F h) := ⟨rfl⟩
local instance globalLaurentLowerMixedMeasurable :
    MeasurableSpace (LowerMixedQuotient F h) := borel _
local instance globalLaurentLowerMixedBorel : BorelSpace (LowerMixedQuotient F h) := ⟨rfl⟩

local instance globalLaurentGLLocallyCompact (a : ℕ) : LocallyCompactSpace (GeneralLinear a F.Carrier) :=
  F.canonicalTopologicalData.generalLinearLocallyCompactSpace a
local instance globalLaurentLowerMeasurable : MeasurableSpace (LowerQuotient h F.Carrier) := borel _
local instance globalLaurentLowerBorel : BorelSpace (LowerQuotient h F.Carrier) := ⟨rfl⟩
local instance globalLaurentLowerHMeasurable :
    MeasurableSpace (lowerBlockUnipotent h F.Carrier) := borel _
local instance globalLaurentLowerHBorel :
    BorelSpace (lowerBlockUnipotent h F.Carrier) := ⟨rfl⟩

/-- Genuine triple-product convergence makes the actual upper coefficient
integrable in the remaining columns. -/
theorem firstBlockUpperCoefficient_integrable_of_product
    (νA : Measure (LeftUnipotentQuotient (m 0) F.Carrier)) [SFinite νA]
    (d : ℤ) (g : GeneralLinear (t + 1) F.Carrier)
    (hprod : Integrable (fun z :
        (Matrix (Fin (m 1 + 1)) (Fin (m 0 + 1)) F.Carrier ×
          LeftUnipotentQuotient (m 0) F.Carrier) ×
            Matrix (Fin j) (Fin (m 1 + 1)) F.Carrier =>
      firstBlockUpperRowAverage F h j k ell f Wtest ν 0 z.1.2 z.1.1 z.2 g)
      (((rectangularMeasure ν (m 1 + 1) (m 0 + 1)).prod
        (νA.restrict (RankinSelberg.determinantSlice F.canonicalTopologicalData (m 0) d))).prod
          (rectangularMeasure ν j (m 1 + 1)))) :
    Integrable (fun Y => firstBlockUpperCoefficient F h j k ell f Wtest ν νA d Y g)
      (rectangularMeasure ν j (m 1 + 1)) := by
  have := TwoBlockLowerUnfolding.sigmaFinite_additiveHaarMeasure ν
  apply hprod.integral_prod_right.congr
  filter_upwards [hprod.prod_left_ae] with Y hY
  exact integral_prod _ hY

/-- The bilateral series of actual lower determinant-slice coefficients. -/
def firstBlockLowerGlobalSeries
    (νMinus : Measure (LowerQuotient h F.Carrier)) : BilateralLaurentSeries :=
  fun d => ∫ z, TwoBlockDominantRectangular.quotientKernel ν ell f Wtest rfl 0 z
    ∂νMinus.restrict (TwoBlockLowerUnipotentQuotient.determinantSlice F h d)

/-- Integrate the actual smaller finite Laurent identity over the remaining
columns and the lower mixed zero quotient. The conclusion uses the actual
large upper JPSS coefficients and actual lower determinant-slice integrals. -/
theorem firstBlock_global_laurent_identity
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (t + (j + k + 1) + 1) F.Carrier) V)
    (hπ : IsOfWhittakerType (t + (j + k + 1))
      (standardCharacter ψ (t + (j + k + 1))) π)
    (hσ : IsSmooth (σ 0))
    (lambda : glFunctionals ψ (t + (j + k + 1)) π)
    (Wmodel : (coefficientModel π lambda).toSubmodule)
    (Wjac : InverseWhittakerFunctions ψ t)
    (hjac : ∀ g : GeneralLinear (t + 1) F.Carrier,
      Wjac.val g = jacquetFunction ψ (fun i => (ell i).val)
        (rectangularMeasure ν (m 0 + 1) (m 1 + 1)) f g)
    (hraw : IsAbsIntegrable ψ (fun i => (ell i).val)
      (rectangularMeasure ν (m 0 + 1) (m 1 + 1)) f)
    (νN : Measure (LeftUnipotentQuotient t F.Carrier)) [SigmaFinite νN]
    (νH : Measure (TwoBlockUnipotentQuotient.BlockQuotient h F.Carrier)) [SigmaFinite νH]
    (νA : Measure (LeftUnipotentQuotient (m 0) F.Carrier)) [SigmaFinite νA]
    (νM : Measure (MixedQuotient F h)) (νL : Measure (LowerMixedQuotient F h))
    (νMinus : Measure (LowerQuotient h F.Carrier))
    (hνN : IsCompatible (upperUnipotent (t + 1) F.Carrier)
      (generalLinearHaar F.Carrier t) (unipotentHaar F.Carrier t) νN)
    (hνH : IsCompatible (TwoBlockUnipotentQuotient.blockUnipotent h F.Carrier)
      (generalLinearHaar F.Carrier t) (TwoBlockUnipotentQuotient.blockHaar F.Carrier h) νH)
    (hνA : IsCompatible (upperUnipotent (m 0 + 1) F.Carrier)
      (generalLinearHaar F.Carrier (m 0)) (unipotentHaar F.Carrier (m 0)) νA)
    (hνM : IsCompatible (mixedSubgroup F h) (generalLinearHaar F.Carrier t)
      (mixedHaar F h) νM)
    (hνL : IsCompatible (lowerMixedSubgroup F h) (generalLinearHaar F.Carrier t)
      (lowerMixedHaar F h) νL)
    (hνMinus : IsCompatible (lowerBlockUnipotent h F.Carrier)
      (generalLinearHaar F.Carrier t) (lowerHaar F h) νMinus)
    (hlower : ∀ d : ℤ,
      Integrable (TwoBlockDominantRectangular.quotientKernel ν ell f Wmodel.val rfl 0)
        (νMinus.restrict (TwoBlockLowerUnipotentQuotient.determinantSlice F h d)) ∧
      Integrable (TwoBlockDominantRectangular.quotientNormProfile ν ell f Wmodel.val rfl 0)
        (νMinus.restrict (TwoBlockLowerUnipotentQuotient.determinantSlice F h d)) ∧
      ∀ᵐ z ∂νMinus.restrict (TwoBlockLowerUnipotentQuotient.determinantSlice F h d),
        TwoBlockDominantRectangular.quotientFiberIntegrable ν ell f Wmodel.val rfl 0 z)
    (D E : LaurentPolynomial ℂ)
    (hsmall : ∀ (Y : Matrix (Fin j) (Fin (m 1 + 1)) F.Carrier)
      (g : GeneralLinear (t + 1) F.Carrier),
      let Zlow : BilateralLaurentSeries :=
        fun d => firstBlockReflectedSmallCoefficient F h j k ell f Wmodel.val ν νA d Y g
      let Zup : BilateralLaurentSeries :=
        fun d => firstBlockUpperCoefficient F h j k ell f Wmodel.val ν νA d Y g
      D • Zlow = E • Zup) :
    let Zlow : BilateralLaurentSeries := fun d =>
      ∫ z, TwoBlockDominantRectangular.quotientKernel ν ell f Wmodel.val rfl 0 z
        ∂νMinus.restrict (TwoBlockLowerUnipotentQuotient.determinantSlice F h d)
    let Zup : BilateralLaurentSeries := fun d =>
      ∫ q, ∫ X, unequalRankIntegrand ψ (normalizedAbsoluteValue F.canonicalTopologicalData)
        j k Wmodel.val Wjac 0 X q ∂rectangularMeasure ν j (t + 1)
          ∂νN.restrict (RankinSelberg.determinantSlice F.canonicalTopologicalData t d)
    D • Zlow = E • Zup := by
  dsimp only at hsmall ⊢
  let hInv := normOneRightInvariant_of_isCompatible F (m 0)
    (generalLinearHaar F.Carrier (m 0)) (unipotentHaar F.Carrier (m 0)) νA hνA
  let μL := νL.restrict (TwoBlockLowerFirstBlockQuotient.determinantSlice F h 0)
  let μY := rectangularMeasure ν j (m 1 + 1)
  let L : LowerMixedQuotient F h → BilateralLaurentSeries :=
    fun q d => firstBlockReflectedQuotientAverage F h j k ell f Wmodel.val ν νA hInv d q
  let U : LowerMixedQuotient F h → BilateralLaurentSeries :=
    fun q d => firstBlockUpperQuotientAverage F h j k ell f Wmodel.val ν νA hInv d q
  have hL (d : ℤ) := firstBlockReflectedQuotientAverage_analysis F h j k ell f ν π
    hπ.1.1 hσ lambda Wmodel νA νL νMinus hνA hνL hνMinus d
      (hlower d).1 (hlower d).2.1 (hlower d).2.2
  have hU (d : ℤ) := firstBlockUpperQuotientAverage_analysis F h j k ell f ν π hπ hσ
    lambda Wmodel (rectangularMeasure ν (m 0 + 1) (m 1 + 1)) hraw
      νN νH νA νM νL hνN hνH hνA hνM hνL d
  have hLi : CoeffwiseIntegrable L μL := fun d => (hL d).2.1
  have hUi : CoeffwiseIntegrable U μL := fun d => (hU d).2.1
  have hLeq := ae_all_iff.mpr (fun d => (hL d).2.2.1)
  have hUeq := ae_all_iff.mpr (fun d => (hU d).2.2.1)
  have heq : ∀ᵐ q ∂μL, D • L q = E • U q := by
    filter_upwards [hLeq, hUeq] with q hl hu
    obtain ⟨g, rfl⟩ := Quotient.exists_rep q
    let s : Matrix (Fin j) (Fin (m 1 + 1)) F.Carrier → BilateralLaurentSeries :=
      fun Y d => firstBlockReflectedSmallCoefficient F h j k ell f Wmodel.val ν νA d Y g
    let v : Matrix (Fin j) (Fin (m 1 + 1)) F.Carrier → BilateralLaurentSeries :=
      fun Y d => firstBlockUpperCoefficient F h j k ell f Wmodel.val ν νA d Y g
    have hs : CoeffwiseIntegrable s μY := fun d => (hl d g rfl).1
    have hv : CoeffwiseIntegrable v μY := fun d =>
      firstBlockUpperCoefficient_integrable_of_product F h j k ell f Wmodel.val ν νA d g
        (hu d g rfl).1
    have hi := integral_laurent_identity_ae (μ := μY) D E hs hv
      (Filter.Eventually.of_forall fun Y => hsmall Y g)
    have hLv : L (Quotient.mk _ g) = coeffwiseIntegral μY s := by
      funext d
      exact (hl d g rfl).2
    have hUv : U (Quotient.mk _ g) = coeffwiseIntegral μY v := by
      funext d
      exact (hu d g rfl).2
    rw [hLv, hUv]
    exact hi
  have hi := integral_laurent_identity_ae (μ := μL) D E hLi hUi heq
  have hLc : coeffwiseIntegral μL L = (fun d =>
      ∫ z, TwoBlockDominantRectangular.quotientKernel ν ell f Wmodel.val rfl 0 z
        ∂νMinus.restrict (TwoBlockLowerUnipotentQuotient.determinantSlice F h d)) := by
    funext d
    exact (hL d).2.2.2
  have hUc : coeffwiseIntegral μL U = (fun d =>
      ∫ q, ∫ X, unequalRankIntegrand ψ (normalizedAbsoluteValue F.canonicalTopologicalData)
        j k Wmodel.val Wjac 0 X q ∂rectangularMeasure ν j (t + 1)
          ∂νN.restrict (RankinSelberg.determinantSlice F.canonicalTopologicalData t d)) := by
    funext d
    exact firstBlockUpperQuotientAverage_integral_eq_large F h j k ell f ν
      π hπ hσ lambda Wmodel Wjac hjac hraw νN νH νA νM νL hνN hνH hνA hνM hνL d
  rw [hLc, hUc] at hi
  exact hi

end Langlands.RankinSelberg.TwoBlockDominantFirstBlock
