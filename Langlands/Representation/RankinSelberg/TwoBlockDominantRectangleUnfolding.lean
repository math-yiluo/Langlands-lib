import Langlands.Representation.RankinSelberg.TwoBlockDominantSectionUnfolding
import Langlands.Representation.RankinSelberg.TwoBlockDominantUpperSliceAnalysis

/-! # Product convergence for the actual rectangular section integrand -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.RankinSelberg.TwoBlockDominantFirstBlock

open MeasureTheory GeneralLinear Whittaker HarmonicAnalysis QuotientIntegration
  TwoBlockJacquet TwoBlockUnipotentQuotient
open scoped ENNReal

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance rectangleUnfoldingTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance rectangleUnfoldingValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance rectangleUnfoldingLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance rectangleUnfoldingT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance rectangleUnfoldingCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance rectangleUnfoldingGLTopology (a : ℕ) :
    IsTopologicalGroup (GeneralLinear a F.Carrier) :=
  F.canonicalTopologicalData.generalLinearTopologicalGroup a
local instance rectangleUnfoldingGLLocalCompact (a : ℕ) :
    LocallyCompactSpace (GeneralLinear a F.Carrier) :=
  F.canonicalTopologicalData.generalLinearLocallyCompactSpace a
local instance rectangleUnfoldingGLCountable (a : ℕ) :
    SecondCountableTopology (GeneralLinear a F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology a
local instance rectangleUnfoldingMeasurable : MeasurableSpace F.Carrier := borel _
local instance rectangleUnfoldingBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance rectangleUnfoldingGLMeasurable (a : ℕ) :
    MeasurableSpace (GeneralLinear a F.Carrier) := borel _
local instance rectangleUnfoldingGLBorel (a : ℕ) :
    BorelSpace (GeneralLinear a F.Carrier) := ⟨rfl⟩
local instance rectangleUnfoldingNMeasurable (a : ℕ) :
    MeasurableSpace (upperUnipotent a F.Carrier) := borel _
local instance rectangleUnfoldingNBorel (a : ℕ) :
    BorelSpace (upperUnipotent a F.Carrier) := ⟨rfl⟩
local instance rectangleUnfoldingNCountable (a : ℕ) :
    SecondCountableTopology (upperUnipotent a F.Carrier) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance rectangleUnfoldingNQMeasurable (a : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient a F.Carrier) := borel _
local instance rectangleUnfoldingNQBorel (a : ℕ) :
    BorelSpace (LeftUnipotentQuotient a F.Carrier) := ⟨rfl⟩

variable {t : ℕ} {m : Fin 2 → ℕ} {h : ∑ i, (m i + 1) = t + 1}
  {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
  {σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i)}
  {ψ : UnitaryAdditiveCharacter F.Carrier}

local instance rectangleUnfoldingHMeasurable :
    MeasurableSpace (blockUnipotent h F.Carrier) := borel _
local instance rectangleUnfoldingHBorel :
    BorelSpace (blockUnipotent h F.Carrier) := ⟨rfl⟩
local instance rectangleUnfoldingHQMeasurable :
    MeasurableSpace (BlockQuotient h F.Carrier) := borel _
local instance rectangleUnfoldingHQBorel :
    BorelSpace (BlockQuotient h F.Carrier) := ⟨rfl⟩

variable (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i))
  (f : Sections F h σ)

/-- At a fixed actual rectangle, the larger-rank test restricts to a Whittaker
function through the diagonal inclusion followed by that rectangle. -/
def rectangularWhittaker (j k : ℕ)
    (Wtest : WhittakerFunctions ψ (t + (j + k + 1)))
    (x : Matrix (Fin j) (Fin (t + 1)) F.Carrier) : WhittakerFunctions ψ t :=
  diagonalWhittaker ψ (j + k + 1)
    (translateWhittaker ψ (t + (j + k + 1)) Wtest (rectangularUnipotent j k x))

@[simp] theorem rectangularWhittaker_apply (j k : ℕ)
    (Wtest : WhittakerFunctions ψ (t + (j + k + 1)))
    (x : Matrix (Fin j) (Fin (t + 1)) F.Carrier)
    (g : GeneralLinear (t + 1) F.Carrier) :
    (rectangularWhittaker F j k Wtest x).val g =
      Wtest.val (unequalRankMatrix j k g x) := rfl

/-- The actual scalar section times the actual unequal-rank test matrix,
descended in its group argument before any rectangular integration. -/
def rectangularSectionIntegrand (j k : ℕ)
    (Wtest : WhittakerFunctions ψ (t + (j + k + 1)))
    (weight : LeftUnipotentQuotient t F.Carrier → ℂ)
    (x : Matrix (Fin j) (Fin (t + 1)) F.Carrier)
    (z : BlockQuotient h F.Carrier) : ℂ :=
  sectionIntegrand F ell f (rectangularWhittaker F j k Wtest x) weight z

@[simp] theorem rectangularSectionIntegrand_mk (j k : ℕ)
    (Wtest : WhittakerFunctions ψ (t + (j + k + 1)))
    (weight : LeftUnipotentQuotient t F.Carrier → ℂ)
    (x : Matrix (Fin j) (Fin (t + 1)) F.Carrier)
    (g : GeneralLinear (t + 1) F.Carrier) :
    rectangularSectionIntegrand F ell f j k Wtest weight x (Quotient.mk _ g) =
      Wtest.val (unequalRankMatrix j k g x) *
        scalarSection (fun i => (ell i).val) f g 1 * weight (Quotient.mk _ g) := rfl

private theorem rectangle_continuous_appendIdentity (n d : ℕ) :
    Continuous (appendIdentity (F := F.Carrier) n d) := by
  induction d with
  | zero => exact continuous_id
  | succ d ih => exact (GeneralLinear.rankInclusionContinuous 1).continuous.comp ih

private theorem rectangle_coefficient_continuous {r : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hπ : IsSmooth π) (lambda : glFunctionals ψ r π)
    (Wtest : (coefficientModel π lambda).toSubmodule) : Continuous Wtest.val.val := by
  obtain ⟨v, rfl⟩ := modelMap_surjective π lambda Wtest
  exact (matrixCoefficient_isLocallyConstant π lambda.val v (hπ v)).continuous

/-- The finite expansion is available also when the supplied functional is zero;
in that case the family is empty. -/
theorem exists_rectangularSectionExpansion (j k : ℕ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (t + (j + k + 1) + 1) F.Carrier) V)
    (hπ : IsOfWhittakerType (t + (j + k + 1))
      (standardCharacter ψ (t + (j + k + 1))) π)
    (lambda : glFunctionals ψ (t + (j + k + 1)) π)
    (Wtest : (coefficientModel π lambda).toSubmodule) :
    ∃ (d : ℕ)
      (φ : Fin d → SchwartzBruhat (Matrix (Fin j) (Fin (t + 1)) F.Carrier))
      (fs : Fin d → (coefficientModel π lambda).toSubmodule),
      ∀ (g : GeneralLinear (t + 1) F.Carrier) x,
        Wtest.val.val (unequalRankMatrix j k g x) =
          ∑ i, φ i x * (fs i).val.val (appendIdentity t (j + k + 1) g) := by
  classical
  by_cases hlambda : lambda.val = 0
  · refine ⟨0, Fin.elim0, Fin.elim0, ?_⟩
    intro g x
    obtain ⟨v, rfl⟩ := modelMap_surjective π lambda Wtest
    change lambda.val (π (unequalRankMatrix j k g x) v) = _
    simp [hlambda]
  · exact unequalRankFiniteExpansion F F.canonicalTopologicalData t j k ψ V π hπ
      lambda hlambda Wtest (unequalRankCompactSupport F F.canonicalTopologicalData
        t j k ψ V π hπ lambda hlambda Wtest)

/-- The finite coefficient expansion gives a literal separated expansion on the
block quotient, retaining the scalar section and quotient weight. -/
theorem rectangularSectionIntegrand_expansion (j k d : ℕ)
    (Wtest : WhittakerFunctions ψ (t + (j + k + 1)))
    (weight : LeftUnipotentQuotient t F.Carrier → ℂ)
    (φ : Fin d → Matrix (Fin j) (Fin (t + 1)) F.Carrier → ℂ)
    (fs : Fin d → WhittakerFunctions ψ (t + (j + k + 1)))
    (he : ∀ (g : GeneralLinear (t + 1) F.Carrier) x,
      Wtest.val (unequalRankMatrix j k g x) =
        ∑ i, φ i x * (fs i).val (appendIdentity t (j + k + 1) g))
    (x : Matrix (Fin j) (Fin (t + 1)) F.Carrier) (z : BlockQuotient h F.Carrier) :
    rectangularSectionIntegrand F ell f j k Wtest weight x z =
      ∑ i, sectionIntegrand F ell f (diagonalWhittaker ψ (j + k + 1) (fs i)) weight z *
        φ i x := by
  induction z using Quotient.inductionOn with
  | h g =>
    simp only [rectangularSectionIntegrand_mk, sectionIntegrand_mk, he,
      diagonalWhittaker, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- Genuine product-space convergence of the actual rectangular section
integrand. The finite expansion, raw Jacquet convergence and fixed-slice compact
norm support supply this independently of every small-block epsilon equation. -/
theorem rectangularSectionIntegrand_integrable (j k : ℕ)
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
    (νH : Measure (BlockQuotient h F.Carrier))
    (hνN : IsCompatible (upperUnipotent (t + 1) F.Carrier)
      (generalLinearHaar F.Carrier t) (unipotentHaar F.Carrier t) νN)
    (hνH : IsCompatible (blockUnipotent h F.Carrier)
      (generalLinearHaar F.Carrier t) (blockHaar F.Carrier h) νH) (a : ℤ) :
    Integrable (fun z : BlockQuotient h F.Carrier ×
        Matrix (Fin j) (Fin (t + 1)) F.Carrier =>
      rectangularSectionIntegrand F ell f j k Wtest.val weight z.2 z.1)
      ((νH.restrict (projection h F.Carrier ⁻¹'
        RankinSelberg.determinantSlice F.canonicalTopologicalData t a)).prod
          (rectangularMeasure ν j (t + 1))) := by
  classical
  obtain ⟨d, φ, fs, he⟩ := exists_rectangularSectionExpansion F j k π hπ lambda Wtest
  have hdiag (i : Fin d) : Integrable
      (sectionIntegrand F ell f (diagonalWhittaker ψ (j + k + 1) (fs i).val) weight)
      (νH.restrict (projection h F.Carrier ⁻¹'
        RankinSelberg.determinantSlice F.canonicalTopologicalData t a)) := by
    have hc : Continuous (diagonalWhittaker ψ (j + k + 1) (fs i).val).val :=
      (rectangle_coefficient_continuous F π hπ.1.1 lambda (fs i)).comp
        (rectangle_continuous_appendIdentity F t (j + k + 1))
    exact (sectionIntegrand_slice_unfolding F ell f _ weight μR hc hw hraw νN νH
      hνN hνH a (diagonalWhittaker_slice_hasCompactSupport F t (j + k) ψ
        π hπ.1.1 lambda (fs i) a)).1
  have hφ (i : Fin d) : Integrable (φ i) (rectangularMeasure ν j (t + 1)) :=
    UnequalRankReduction.padic_rectangular_schwartz_integrable
      F F.canonicalTopologicalData j (t + 1) ν (φ i)
  simp_rw [rectangularSectionIntegrand_expansion F ell f j k d Wtest.val weight
    (fun i => (φ i : _ → ℂ)) (fun i => (fs i).val) he]
  exact UnequalRankReduction.integrable_separated_sum Finset.univ _ _
    (fun i _ => hdiag i) (fun i _ => hφ i)

end Langlands.RankinSelberg.TwoBlockDominantFirstBlock
