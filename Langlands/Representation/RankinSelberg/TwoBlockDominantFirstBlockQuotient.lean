import Langlands.Representation.RankinSelberg.TwoBlockDominantRectangleUnfolding
import Langlands.Representation.RankinSelberg.TwoBlockFirstBlockQuotientIntegrationProof

/-! # First-block disintegration of the actual rectangular section average -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.RankinSelberg.TwoBlockDominantFirstBlock

open MeasureTheory ProbabilityTheory GeneralLinear Whittaker HarmonicAnalysis QuotientIntegration
  TwoBlockJacquet TwoBlockUnipotentQuotient
open scoped ENNReal

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance firstQuotientTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance firstQuotientValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance firstQuotientLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance firstQuotientT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance firstQuotientCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance firstQuotientGLTopology (a : ℕ) :
    IsTopologicalGroup (GeneralLinear a F.Carrier) :=
  F.canonicalTopologicalData.generalLinearTopologicalGroup a
local instance firstQuotientGLLocalCompact (a : ℕ) :
    LocallyCompactSpace (GeneralLinear a F.Carrier) :=
  F.canonicalTopologicalData.generalLinearLocallyCompactSpace a
local instance firstQuotientGLCountable (a : ℕ) :
    SecondCountableTopology (GeneralLinear a F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology a
local instance firstQuotientMeasurable : MeasurableSpace F.Carrier := borel _
local instance firstQuotientBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance firstQuotientGLMeasurable (a : ℕ) :
    MeasurableSpace (GeneralLinear a F.Carrier) := borel _
local instance firstQuotientGLBorel (a : ℕ) :
    BorelSpace (GeneralLinear a F.Carrier) := ⟨rfl⟩
local instance firstQuotientNMeasurable (a : ℕ) :
    MeasurableSpace (upperUnipotent a F.Carrier) := borel _
local instance firstQuotientNBorel (a : ℕ) :
    BorelSpace (upperUnipotent a F.Carrier) := ⟨rfl⟩
local instance firstQuotientNCountable (a : ℕ) :
    SecondCountableTopology (upperUnipotent a F.Carrier) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance firstQuotientNQMeasurable (a : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient a F.Carrier) := borel _
local instance firstQuotientNQBorel (a : ℕ) :
    BorelSpace (LeftUnipotentQuotient a F.Carrier) := ⟨rfl⟩

variable {t : ℕ} {m : Fin 2 → ℕ} {h : ∑ i, (m i + 1) = t + 1}
  {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
  {σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i)}
  {ψ : UnitaryAdditiveCharacter F.Carrier}

local instance firstQuotientHMeasurable :
    MeasurableSpace (blockUnipotent h F.Carrier) := borel _
local instance firstQuotientHBorel :
    BorelSpace (blockUnipotent h F.Carrier) := ⟨rfl⟩
local instance firstQuotientHQMeasurable :
    MeasurableSpace (BlockQuotient h F.Carrier) := borel _
local instance firstQuotientHQBorel :
    BorelSpace (BlockQuotient h F.Carrier) := ⟨rfl⟩

local instance firstQuotientMixedSubgroupMeasurable :
    MeasurableSpace (TwoBlockFirstBlockQuotient.mixedSubgroup F h) := borel _
local instance firstQuotientMixedSubgroupBorel :
    BorelSpace (TwoBlockFirstBlockQuotient.mixedSubgroup F h) := ⟨rfl⟩
local instance firstQuotientMixedMeasurable :
    MeasurableSpace (TwoBlockFirstBlockQuotient.MixedQuotient F h) := borel _
local instance firstQuotientMixedBorel :
    BorelSpace (TwoBlockFirstBlockQuotient.MixedQuotient F h) := ⟨rfl⟩

variable (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i))
  (f : Sections F h σ)

/-- Integrate the actual external rectangle before using the first-block tower. -/
def rectangularSectionAverage (j k : ℕ)
    (Wtest : WhittakerFunctions ψ (t + (j + k + 1)))
    (ν : AdditiveHaarMeasure F.Carrier)
    (weight : LeftUnipotentQuotient t F.Carrier → ℂ)
    (z : BlockQuotient h F.Carrier) : ℂ :=
  ∫ x, rectangularSectionIntegrand F ell f j k Wtest weight x z
    ∂rectangularMeasure ν j (t + 1)

private theorem firstQuotient_continuous_appendIdentity (n d : ℕ) :
    Continuous (appendIdentity (F := F.Carrier) n d) := by
  induction d with
  | zero => exact continuous_id
  | succ d ih => exact (GeneralLinear.rankInclusionContinuous 1).continuous.comp ih

/-- Finite coefficient expansion gives joint continuity and pointwise rectangle
convergence, including an empty family for a zero supplied functional. -/
theorem rectangularSectionIntegrand_regular (j k : ℕ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (t + (j + k + 1) + 1) F.Carrier) V)
    (hπ : IsOfWhittakerType (t + (j + k + 1))
      (standardCharacter ψ (t + (j + k + 1))) π)
    (lambda : glFunctionals ψ (t + (j + k + 1)) π)
    (Wtest : (coefficientModel π lambda).toSubmodule)
    (ν : AdditiveHaarMeasure F.Carrier)
    (weight : LeftUnipotentQuotient t F.Carrier → ℂ) (hw : Continuous weight) :
    Continuous (fun z : BlockQuotient h F.Carrier ×
        Matrix (Fin j) (Fin (t + 1)) F.Carrier =>
      rectangularSectionIntegrand F ell f j k Wtest.val weight z.2 z.1) ∧
    (∀ z, Integrable (fun x =>
      rectangularSectionIntegrand F ell f j k Wtest.val weight x z)
      (rectangularMeasure ν j (t + 1))) ∧
    Continuous (rectangularSectionAverage F ell f j k Wtest.val ν weight) := by
  classical
  obtain ⟨d, φ, fs, he⟩ := exists_rectangularSectionExpansion F j k π hπ lambda Wtest
  let D (i : Fin d) := sectionIntegrand F ell f
    (diagonalWhittaker ψ (j + k + 1) (fs i).val) weight
  have hD (i : Fin d) : Continuous (D i) := by
    apply sectionIntegrand_continuous F ell f _ weight _ hw
    exact (glModelFunction_continuous ψ _ π hπ.1.1 lambda (fs i)).comp
      (firstQuotient_continuous_appendIdentity F t (j + k + 1))
  have hφ (i : Fin d) : Integrable (φ i) (rectangularMeasure ν j (t + 1)) :=
    UnequalRankReduction.padic_rectangular_schwartz_integrable
      F F.canonicalTopologicalData j (t + 1) ν (φ i)
  have e (x : Matrix (Fin j) (Fin (t + 1)) F.Carrier)
      (z : BlockQuotient h F.Carrier) :
      rectangularSectionIntegrand F ell f j k Wtest.val weight x z =
        ∑ i, D i z * φ i x :=
    rectangularSectionIntegrand_expansion F ell f j k d Wtest.val weight
      (fun i => (φ i : _ → ℂ)) (fun i => (fs i).val) he x z
  refine ⟨?_, ?_, ?_⟩
  · simp_rw [e]
    exact continuous_finsetSum _ fun i _ =>
      ((hD i).comp continuous_fst).mul ((φ i).continuous.comp continuous_snd)
  · intro z
    simp_rw [e]
    exact integrable_finsetSum _ fun i _ => (hφ i).const_mul (D i z)
  · have eavg : rectangularSectionAverage F ell f j k Wtest.val ν weight =
        fun z => ∑ i, D i z * ∫ x, φ i x ∂rectangularMeasure ν j (t + 1) := by
      funext z
      unfold rectangularSectionAverage
      simp_rw [e]
      rw [integral_finsetSum _ (fun i _ => (hφ i).const_mul (D i z))]
      simp_rw [integral_const_mul]
    rw [eavg]
    exact continuous_finsetSum _ fun i _ => (hD i).mul_const _

/-- Exact first-block quotient unfolding of the actual rectangle average, at
small slice `a` over the fixed mixed slice zero. -/
theorem rectangularSectionAverage_firstBlock_unfolding (j k : ℕ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (t + (j + k + 1) + 1) F.Carrier) V)
    (hπ : IsOfWhittakerType (t + (j + k + 1))
      (standardCharacter ψ (t + (j + k + 1))) π)
    (lambda : glFunctionals ψ (t + (j + k + 1)) π)
    (Wtest : (coefficientModel π lambda).toSubmodule)
    (weight : LeftUnipotentQuotient t F.Carrier → ℂ) (hw : Continuous weight)
    (μR : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier))
    [μR.IsAddHaarMeasure] (hraw : IsAbsIntegrable ψ (fun i => (ell i).val) μR f)
    (ν : AdditiveHaarMeasure F.Carrier)
    (νN : Measure (LeftUnipotentQuotient t F.Carrier))
    (νH : Measure (BlockQuotient h F.Carrier)) [SigmaFinite νH]
    (νA : Measure (LeftUnipotentQuotient (m 0) F.Carrier)) [SigmaFinite νA]
    (νM : Measure (TwoBlockFirstBlockQuotient.MixedQuotient F h))
    (hνN : IsCompatible (upperUnipotent (t + 1) F.Carrier)
      (generalLinearHaar F.Carrier t) (unipotentHaar F.Carrier t) νN)
    (hνH : IsCompatible (blockUnipotent h F.Carrier)
      (generalLinearHaar F.Carrier t) (blockHaar F.Carrier h) νH)
    (hνA : IsCompatible (upperUnipotent (m 0 + 1) F.Carrier)
      (generalLinearHaar F.Carrier (m 0)) (unipotentHaar F.Carrier (m 0)) νA)
    (hνM : IsCompatible (TwoBlockFirstBlockQuotient.mixedSubgroup F h)
      (generalLinearHaar F.Carrier t) (TwoBlockFirstBlockQuotient.mixedHaar F h) νM)
    (a : ℤ) :
    let hInv := TwoBlockFirstBlockQuotient.normOneRightInvariant_of_isCompatible F (m 0)
      (generalLinearHaar F.Carrier (m 0)) (unipotentHaar F.Carrier (m 0)) νA hνA
    let E := rectangularSectionAverage F ell f j k Wtest.val ν weight
    let B := TwoBlockFirstBlockQuotient.firstBlockAverage F h νA hInv a E
    let μM := νM.restrict (TwoBlockFirstBlockQuotient.determinantSlice F h 0)
    Measurable B ∧ Integrable B μM ∧
      (∫ z, E z ∂νH.restrict (TwoBlockUnipotentQuotient.determinantSlice F h a)) =
        ∫ q, B q ∂μM := by
  dsimp only
  let hInv := TwoBlockFirstBlockQuotient.normOneRightInvariant_of_isCompatible F (m 0)
    (generalLinearHaar F.Carrier (m 0)) (unipotentHaar F.Carrier (m 0)) νA hνA
  let κ := TwoBlockFirstBlockQuotient.fiberKernel F h νA hInv a
  have hκ := TwoBlockFirstBlockQuotient.fiberKernel_mk F h νA hInv a
  have hzero := (TwoBlockFirstBlockQuotient.normalized_tower F h
    νA hInv hνA νM hνM νH hνH).2
  have hcomp := TwoBlockFirstBlockQuotient.fiberKernel_comp_zeroSlice_eq F h
    νA hInv hνA νM hνM νH hzero a
  have hEc := (rectangularSectionIntegrand_regular F ell f j k π hπ lambda Wtest ν
    weight hw).2.2
  have hEp := rectangularSectionIntegrand_integrable F ell f j k π hπ lambda Wtest
    weight hw μR hraw ν νN νH hνN hνH a
  have hEi := hEp.integral_prod_left
  have he := TwoBlockFirstBlockQuotient.firstBlockAverage_eq_integral_kernel F h νA
    hInv a κ hκ _ hEc.measurable
  have hBm : Measurable (TwoBlockFirstBlockQuotient.firstBlockAverage F h νA hInv a
      (rectangularSectionAverage F ell f j k Wtest.val ν weight)) := by
    rw [he]
    exact (hEc.measurable.stronglyMeasurable.integral_kernel (κ := κ)).measurable
  have hBo := ((TwoBlockFirstBlockQuotient.analytic_of_comp_eq F h νA hInv a κ hκ
    _ _ hcomp).2 _ hEc.measurable).2 hEi
  exact ⟨hBm, hBo⟩

end Langlands.RankinSelberg.TwoBlockDominantFirstBlock
