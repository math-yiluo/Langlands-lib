import Langlands.Representation.RankinSelberg.TwoBlockDominantModelRealization
import Langlands.Representation.RankinSelberg.TwoBlockFirstBlockLaurentIdentityProof
import Langlands.Representation.RankinSelberg.UnequalRankFunctionalEquationProof

/-!
# First-block Laurent laws for actual equal-rank Jacquet coefficients

The ordinary Jacquet realization and the published first-block theorem supply
the actual law at all sufficiently large real deformation parameters.
-/

noncomputable section

namespace Langlands.RankinSelberg.DominantRankTransport

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration
  LaurentPolynomial

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
  {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

local instance equalFirstBlockTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance equalFirstBlockValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance equalFirstBlockLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance equalFirstBlockT2 : T2Space F.Carrier :=
  F.canonicalTopologicalData.fieldT2
local instance equalFirstBlockSecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance equalFirstBlockMeasurable : MeasurableSpace F.Carrier := borel _
local instance equalFirstBlockBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance equalFirstBlockGLMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear (n + 1) F.Carrier) := borel _
local instance equalFirstBlockGLBorel (n : ℕ) :
    BorelSpace (GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance equalFirstBlockUnipotentMeasurable (n : ℕ) :
    MeasurableSpace (upperUnipotent (n + 1) F.Carrier) := borel _
local instance equalFirstBlockUnipotentBorel (n : ℕ) :
    BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
local instance equalFirstBlockQuotientMeasurable (n : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient n F.Carrier) := borel _
local instance equalFirstBlockQuotientBorel (n : ℕ) :
    BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
local instance equalFirstBlockLowerMeasurable :
    MeasurableSpace (TwoBlockLowerUnipotentQuotient.LowerQuotient h F.Carrier) :=
  borel _
local instance equalFirstBlockLowerBorel :
    BorelSpace (TwoBlockLowerUnipotentQuotient.LowerQuotient h F.Carrier) := ⟨rfl⟩

local notation "qF" => F.canonicalTopologicalData.residueCardinality
local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData

include h in
/-- The first positive block is strictly smaller than the sum of both blocks. -/
theorem firstBlock_lt_total : m 0 < t := by
  have hsum : (m 0 + 1) + (m 1 + 1) = t + 1 := by
    simpa only [Fin.sum_univ_two] using h
  omega

variable (ψ : UnitaryAdditiveCharacter F.Carrier)
  (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ (GeneralLinear (t + 1) F.Carrier) V)
  (lambda : glFunctionals ψ t π)
  (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i))
  (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i))
  (J : glInverseFunctionals ψ t (TwoBlockJacquet.inducedRep F h σ))
  (μN : Measure (LeftUnipotentQuotient t F.Carrier))
  (μA : Measure (LeftUnipotentQuotient (m 0) F.Carrier))

/-- The actual lower quotient coefficient series of the equal-rank
first-block unfolding, retaining both supplied measures. -/
def equalFirstBlockLowerSeries
    (f : TwoBlockJacquet.Sections F h σ)
    (Wtest : (coefficientModel π lambda).toSubmodule)
    (Φ : SchwartzBruhat (Fin (t + 1) → F.Carrier)) : BilateralLaurentSeries :=
  fun k => ∫ z, TwoBlockLowerUnfolding.integrand ell f Wtest.val Φ ν.val z
    ∂(Measure.map
      (TwoBlockLowerUnipotentQuotient.lowerToStandard h F.Carrier).symm μN).restrict
        (TwoBlockLowerUnipotentQuotient.determinantSlice F h k)

/-- One epsilon monomial and one normalized polynomial pair, common to all
sections, model coefficients and row tests, give the actual first-block law. -/
def EqualFirstBlockCoefficientLaw : Prop :=
  ∃ (ζ c : ℂˣ) (d : ℤ) (P Pdual : Polynomial ℂ),
    UnequalRankEpsilonEquation (firstBlock_lt_total h) qF ψ abv μA ν.val
      π (σ 0) lambda (ell 0) c d ∧
    HasModelMinusOneScalar (σ 0) (ell 0) ζ ∧
    (∀ (j k : ℕ) (hr : t = m 0 + (j + k + 1)),
      IsNormalizedGenerator
        (unequalRankValuesAt j k hr qF ψ abv μA
          (rectangularMeasure ν.val j (m 0 + 1)) π (σ 0) lambda (ell 0)) P ∧
      IsNormalizedGenerator
        (dualUnequalRankRationalValuesAt (firstBlock_lt_total h) j k hr
          qF ψ abv μA ν.val π (σ 0) lambda (ell 0)) Pdual) ∧
    ∀ (f : TwoBlockJacquet.Sections F h σ)
      (Wtest : (coefficientModel π lambda).toSubmodule)
      (Φ : SchwartzBruhat (Fin (t + 1) → F.Carrier)),
      let a : BilateralLaurentSeries :=
        equalRankSliceCoefficient F.canonicalTopologicalData μN ψ Wtest.val
          (modelMap (TwoBlockJacquet.inducedRep F h σ) J f).val Φ
      let b := equalFirstBlockLowerSeries F h ψ ν π lambda σ ell μN f Wtest Φ
      Polynomial.eval₂ C (C ((qF : ℂ)⁻¹) * T (-1)) Pdual • b =
        (C ((ζ : ℂ) ^ t * (c : ℂ)) * T d * P.toLaurent) • a

omit σ ell J μN μA in
/-- Genuine ordinary Jacquet functionals and the actual first-block Laurent
law exist above one bound, uniformly over both compatible quotient measures.
The small-pair epsilon equation is derived from the published theorem. -/
theorem exists_equalFirstBlockCoefficientLaw
    [Measure.IsMulRightInvariant (unipotentHaar F.Carrier t)]
    [Measure.IsMulRightInvariant (unipotentHaar F.Carrier (m 0))]
    (hπ : IsOfWhittakerType t (standardCharacter ψ t) π)
    (hlambda : lambda.val ≠ 0)
    (τ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i))
    (hτ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (τ i))
    (ell0 : ∀ i, glInverseFunctionals ψ (m i) (τ i))
    (hell0 : ∀ i, (ell0 i).val ≠ 0) :
    ∃ Cbound : ℝ, ∀ u : ℝ, Cbound < u →
      let σu := twoBlockOppositeTwistBlocks F m τ u
      let ellu := fun i => twoBlockOppositeTwistFunctional F m ψ τ u i (ell0 i)
      let μR := rectangularMeasure ν.val (m 0 + 1) (m 1 + 1)
      (∀ f : TwoBlockJacquet.Sections F h σu,
        TwoBlockJacquet.IsAbsIntegrable ψ (fun i => (ell0 i).val) μR f) ∧
      ∃ Ju : glInverseFunctionals ψ t (TwoBlockJacquet.inducedRep F h σu),
        Ju.val ≠ 0 ∧
        (∀ (f : TwoBlockJacquet.Sections F h σu)
          (g : GeneralLinear (t + 1) F.Carrier),
          Ju.val (TwoBlockJacquet.inducedRep F h σu g f) =
            TwoBlockJacquet.jacquetFunction ψ (fun i => (ellu i).val) μR f g) ∧
        ∀ (μN : Measure (LeftUnipotentQuotient t F.Carrier))
          (μA : Measure (LeftUnipotentQuotient (m 0) F.Carrier)),
          IsCompatible (upperUnipotent (t + 1) F.Carrier)
            (generalLinearHaar F.Carrier t) (unipotentHaar F.Carrier t) μN →
          IsCompatible (upperUnipotent (m 0 + 1) F.Carrier)
            (generalLinearHaar F.Carrier (m 0)) (unipotentHaar F.Carrier (m 0)) μA →
          EqualFirstBlockCoefficientLaw F h ψ ν π lambda σu ellu Ju μN μA := by
  obtain ⟨_, _, _, _, hFirst⟩ :=
    twoBlockFirstBlockLaurentIdentity.{uF,uV,uW} p F ψ ν t m h
  obtain ⟨Cfirst, hCfirst⟩ := hFirst π hπ lambda τ hτ ell0
  obtain ⟨Cjac, hCjac⟩ := twoBlockOrdinaryJacquetFunctional p F ψ ν t m h τ hτ ell0 hell0
  refine ⟨max Cfirst Cjac, fun u hu => ?_⟩
  let σu := twoBlockOppositeTwistBlocks F m τ u
  let ellu := fun i => twoBlockOppositeTwistFunctional F m ψ τ u i (ell0 i)
  let μR := rectangularMeasure ν.val (m 0 + 1) (m 1 + 1)
  obtain ⟨habs, Ju, hJu0, hJu⟩ := hCjac u (lt_of_le_of_lt (le_max_right _ _) hu)
  refine ⟨habs, Ju, hJu0, hJu, ?_⟩
  intro μN μA hμN hμA
  obtain ⟨_, _, _, _, hLaurent⟩ :=
    hCfirst u (lt_of_le_of_lt (le_max_left _ _) hu) μN μA hμN hμA
  have hσ0 : IsOfWhittakerType (m 0) (inverseStandardCharacter ψ (m 0)) (σu 0) :=
    (twoBlockOppositeTwistBlocks_isOfWhittakerType_iff F m τ u 0 _).2
      ((isOfWhittakerType_standard_iff_inverse ψ (τ 0)).1 (hτ 0))
  have heq := unequalRankFunctionalEquation F F.canonicalTopologicalData (m 0) t
    (firstBlock_lt_total h) ψ μA hμA ν.val ν.property V (W 0) π (σu 0)
    hπ hσ0 lambda (ellu 0) hlambda (hell0 0)
  obtain ⟨c, d, hEpsilon⟩ := exists_unequalRankEpsilonEquation_iff.mpr heq
  obtain ⟨ζ, P, Pdual, hζ, hBody, hLaw⟩ := hLaurent c d hEpsilon
  refine ⟨ζ, c, d, P, Pdual, hEpsilon, hζ,
    fun j k hr => ⟨(hBody j k hr).1, (hBody j k hr).2.1⟩, ?_⟩
  intro f Wtest Φ
  have ha := hLaw f Wtest Φ
  change _ = _ at ha
  change _ = _
  rw [← unfoldedJacquetSeries_eq F h ψ σu ellu μR μN Ju hJu f Wtest.val Φ]
  exact ha

end Langlands.RankinSelberg.DominantRankTransport
