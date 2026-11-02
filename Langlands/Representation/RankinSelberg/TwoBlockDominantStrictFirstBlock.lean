import Langlands.Representation.RankinSelberg.TwoBlockDominantFirstBlockLaurentIdentityStatement
import Langlands.Representation.RankinSelberg.TwoBlockDominantStrictNumerators
import Langlands.Representation.RankinSelberg.TwoBlockDominantEqualSecondBlock

noncomputable section

namespace Langlands.RankinSelberg.DominantRankTransport

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration
  LaurentPolynomial

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  {t r : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
  {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

local instance strictFirstBlockTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance strictFirstBlockValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance strictFirstBlockLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance strictFirstBlockT2 : T2Space F.Carrier :=
  F.canonicalTopologicalData.fieldT2
local instance strictFirstBlockSecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance strictFirstBlockMeasurable : MeasurableSpace F.Carrier := borel _
local instance strictFirstBlockBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance strictFirstBlockGLMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear (n + 1) F.Carrier) := borel _
local instance strictFirstBlockGLBorel (n : ℕ) :
    BorelSpace (GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance strictFirstBlockUnipotentMeasurable (n : ℕ) :
    MeasurableSpace (upperUnipotent (n + 1) F.Carrier) := borel _
local instance strictFirstBlockUnipotentBorel (n : ℕ) :
    BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
local instance strictFirstBlockQuotientMeasurable (n : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient n F.Carrier) := borel _
local instance strictFirstBlockQuotientBorel (n : ℕ) :
    BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
local instance strictFirstBlockLowerMeasurable :
    MeasurableSpace (TwoBlockLowerUnipotentQuotient.LowerQuotient h F.Carrier) :=
  borel _
local instance strictFirstBlockLowerBorel :
    BorelSpace (TwoBlockLowerUnipotentQuotient.LowerQuotient h F.Carrier) := ⟨rfl⟩

local notation "qF" => F.canonicalTopologicalData.residueCardinality
local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData

variable (htr : t < r)
  (ψ : UnitaryAdditiveCharacter F.Carrier)
  (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
  (lambda : glFunctionals ψ r π)
  (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i))
  (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i))

/-- Retained complete first-block witnesses at a strictly dominant test rank. -/
def StrictFirstBlockFactorCertificate
    (μA : Measure (LeftUnipotentQuotient (m 0) F.Carrier))
    (ζ c : ℂˣ) (d : ℤ) (P Pdual : Polynomial ℂ) : Prop :=
  UnequalRankEpsilonEquation (lt_trans (firstBlock_lt_total h) htr) qF ψ abv μA ν.val
    π (σ 0) lambda (ell 0) c d ∧
  HasModelMinusOneScalar (σ 0) (ell 0) ζ ∧
  ∀ (j k : ℕ) (hr : r = m 0 + (j + k + 1)),
    IsNormalizedGenerator
      (unequalRankValuesAt j k hr qF ψ abv μA
        (rectangularMeasure ν.val j (m 0 + 1)) π (σ 0) lambda (ell 0)) P ∧
    IsNormalizedGenerator
      (dualUnequalRankRationalValuesAt (lt_trans (firstBlock_lt_total h) htr) j k hr
        qF ψ abv μA ν.val π (σ 0) lambda (ell 0)) Pdual

variable (J : glInverseFunctionals ψ t (TwoBlockJacquet.inducedRep F h σ))
  (μN : Measure (LeftUnipotentQuotient t F.Carrier))
  (μA : Measure (LeftUnipotentQuotient (m 0) F.Carrier))

/-- One retained epsilon monomial and normalized polynomial pair work for
all complementary rows, sections and actual large-model coefficients. -/
def StrictFirstBlockCoefficientLaw : Prop :=
  ∃ (ζ c : ℂˣ) (d : ℤ) (P Pdual : Polynomial ℂ),
    StrictFirstBlockFactorCertificate F h htr ψ ν π lambda σ ell μA ζ c d P Pdual ∧
    ∀ (j k : ℕ) (hr : r = t + (j + k + 1))
      (f : TwoBlockJacquet.Sections F h σ)
      (Wtest : (coefficientModel π lambda).toSubmodule),
      let a := strictSliceCoefficient F hr ψ μN ν.val Wtest.val
        (modelMap (TwoBlockJacquet.inducedRep F h σ) J f).val
      let b : BilateralLaurentSeries :=
        TwoBlockDominantRectangular.kernelSliceCoefficient ν.val ell f Wtest.val μN hr
      Polynomial.eval₂ C (C ((qF : ℂ)⁻¹) * T (-1)) Pdual • b =
        (C ((ζ : ℂ) ^ r * (c : ℂ)) * T d * P.toLaurent) • a

omit σ ell J μN μA in
/-- The independently owned closed first-block result supplies a common bound
for any functional realizing the same actual ordinary Jacquet integral. -/
theorem exists_strictFirstBlockBound_forOrdinaryFunctional
    (H : TwoBlockDominantFirstBlockLaurentIdentityStatement.{uF,uV,uW})
    [Measure.IsMulRightInvariant (unipotentHaar F.Carrier t)]
    [Measure.IsMulRightInvariant (unipotentHaar F.Carrier (m 0))]
    (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
    (hlambda : lambda.val ≠ 0)
    (τ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i))
    (hτ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (τ i))
    (ell0 : ∀ i, glInverseFunctionals ψ (m i) (τ i))
    (hell0 : ∀ i, (ell0 i).val ≠ 0) :
    ∃ Cbound : ℝ, ∀ u : ℝ, Cbound < u →
      ∀ (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i)),
        σ = twoBlockOppositeTwistBlocks F m τ u →
      ∀ (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i)),
        (∀ i, (ell i).val = (ell0 i).val) →
      ∀ (J : glInverseFunctionals ψ t (TwoBlockJacquet.inducedRep F h σ)),
        (∀ (f : TwoBlockJacquet.Sections F h σ)
          (g : GeneralLinear (t + 1) F.Carrier),
          J.val (TwoBlockJacquet.inducedRep F h σ g f) =
            TwoBlockJacquet.jacquetFunction ψ (fun i => (ell i).val)
              (rectangularMeasure ν.val (m 0 + 1) (m 1 + 1)) f g) →
      ∀ (μN : Measure (LeftUnipotentQuotient t F.Carrier))
        (μA : Measure (LeftUnipotentQuotient (m 0) F.Carrier)),
        IsCompatible (upperUnipotent (t + 1) F.Carrier)
          (generalLinearHaar F.Carrier t) (unipotentHaar F.Carrier t) μN →
        IsCompatible (upperUnipotent (m 0 + 1) F.Carrier)
          (generalLinearHaar F.Carrier (m 0)) (unipotentHaar F.Carrier (m 0)) μA →
        StrictFirstBlockCoefficientLaw F h htr ψ ν π lambda σ ell J μN μA := by
  obtain ⟨Cbound, hC⟩ := (H p F ψ ν t r m h htr).2 π hπ lambda τ hτ ell0
  refine ⟨Cbound, fun u hu σ hσ ell hell J hJ μN μA hμN hμA => ?_⟩
  subst σ
  have hellEq : ell = fun i => twoBlockOppositeTwistFunctional F m ψ τ u i (ell0 i) := by
    funext i
    exact Subtype.ext (hell i)
  subst ell
  obtain ⟨-, J₀, -, hJ₀, hBody⟩ := hC u hu
  have hJEq : J = J₀ := by
    apply Subtype.ext
    ext f
    have he := (hJ f 1).trans (hJ₀ f 1).symm
    simpa only [map_one, Module.End.one_apply] using he
  subst J₀
  obtain ⟨-, -, -, -, hLaurent⟩ := hBody inferInstance inferInstance μN μA hμN hμA
  let σu := twoBlockOppositeTwistBlocks F m τ u
  let ellu := fun i => twoBlockOppositeTwistFunctional F m ψ τ u i (ell0 i)
  have hσ0 : IsOfWhittakerType (m 0) (inverseStandardCharacter ψ (m 0)) (σu 0) :=
    (twoBlockOppositeTwistBlocks_isOfWhittakerType_iff F m τ u 0 _).mpr
      ((isOfWhittakerType_standard_iff_inverse ψ (τ 0)).mp (hτ 0))
  have hEq := unequalRankFunctionalEquation F F.canonicalTopologicalData (m 0) r
    (lt_trans (firstBlock_lt_total h) htr) ψ μA hμA ν.val ν.property V (W 0) π (σu 0)
    hπ hσ0 lambda (ellu 0) hlambda (hell0 0)
  obtain ⟨c, d, hε⟩ := exists_unequalRankEpsilonEquation_iff.mpr hEq
  obtain ⟨ζ, P, Pdual, hζ, hgen, hLaw⟩ := hLaurent c d hε
  refine ⟨ζ, c, d, P, Pdual, ⟨hε, hζ,
    fun j k hr => ⟨(hgen j k hr).1, (hgen j k hr).2.1⟩⟩, ?_⟩
  intro j k hr f Wtest
  exact hLaw j k hr f Wtest

omit σ ell J μN μA in
set_option maxHeartbeats 1600000 in
/-- A common bound supplies a nonzero ordinary functional and its strict
first-block law, conditional on the independently owned analytic theorem. -/
theorem exists_strictFirstBlockCoefficientLaw
    (H : TwoBlockDominantFirstBlockLaurentIdentityStatement.{uF,uV,uW})
    [Measure.IsMulRightInvariant (unipotentHaar F.Carrier t)]
    [Measure.IsMulRightInvariant (unipotentHaar F.Carrier (m 0))]
    (hπ : IsOfWhittakerType r (standardCharacter ψ r) π)
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
          StrictFirstBlockCoefficientLaw F h htr ψ ν π lambda σu ellu Ju μN μA := by
  obtain ⟨Cfirst, hFirst⟩ := exists_strictFirstBlockBound_forOrdinaryFunctional
    F h htr ψ ν π lambda H hπ hlambda τ hτ ell0 hell0
  obtain ⟨Cjac, hJac⟩ := twoBlockOrdinaryJacquetFunctional p F ψ ν t m h τ hτ ell0 hell0
  refine ⟨max Cfirst Cjac, fun u hu => ?_⟩
  dsimp only
  obtain ⟨habs, J, hJ0, hJ⟩ := hJac u (lt_of_le_of_lt (le_max_right _ _) hu)
  refine ⟨habs, J, hJ0, hJ, ?_⟩
  intro μN μA hμN hμA
  exact hFirst u (lt_of_le_of_lt (le_max_left _ _) hu)
    (twoBlockOppositeTwistBlocks F m τ u) rfl
    (fun i => twoBlockOppositeTwistFunctional F m ψ τ u i (ell0 i))
    (fun _ => rfl) J hJ μN μA hμN hμA

end Langlands.RankinSelberg.DominantRankTransport
