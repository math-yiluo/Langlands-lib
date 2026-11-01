import Langlands.Representation.RankinSelberg.TwoBlockOrdinaryJacquetFunctionalProof
import Langlands.Representation.RankinSelberg.TwoBlockUnfoldingIntegrandData
import Langlands.Representation.RankinSelberg.EqualRankSliceSupportProof
import Langlands.Representation.RankinSelberg.NormalizedProductWhittakerTypeProof
import Langlands.Representation.RankinSelberg.WhittakerGammaAdapters
import Langlands.Representation.Induction.OppositeProductReversalProof

/-!
# Actual Jacquet coefficient series at the equal-rank boundary

Internal assembly of the published ordinary Jacquet realization, normalized
induction type preservation, quotient integrand and lower-support theorem.
-/

noncomputable section

namespace Langlands.RankinSelberg.DominantRankTransport

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration
  TwoBlockUnipotentQuotient

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)
  {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

/-- Full inverse-standard type of the actual lower induction, obtained by
reversing all sizes, carriers and representations before using upper type. -/
theorem lowerInduced_inverseWhittakerType
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i))
    (hσ : ∀ i, letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i)) :
    letI := F.canonicalTopologicalData.topology
    IsOfWhittakerType t (inverseStandardCharacter ψ t)
      (TwoBlockJacquet.inducedRep F h σ) := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  obtain ⟨E, -, -⟩ := glOppositeProductReversal p F F.canonicalTopologicalData
    (t + 1) (succBlockShape m h) W σ (fun i => (hσ i).1.1)
  have hrev : ∑ i : Fin 2, (m i.rev + 1) = t + 1 :=
    (Equiv.sum_comp Fin.revPerm (fun i => m i + 1)).trans h
  have hupper := normalizedProductWhittakerType p F ψ t 2 (fun i => m i.rev) hrev
    (W := fun i => W i.rev) (fun i => σ i.rev) (fun i => hσ i.rev)
  exact (isOfWhittakerType_standard_iff_inverse ψ _).1 (hupper.of_equiv E.symm)

section Series

local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance : MeasurableSpace F.Carrier := borel F.Carrier
local instance : BorelSpace F.Carrier := ⟨rfl⟩

variable (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
  (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i))
  (ell : letI := F.canonicalTopologicalData.topology; ∀ i, glInverseFunctionals ψ (m i) (σ i))
  (μR : letI := borel F.Carrier;
    Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier))
  [μR.IsAddHaarMeasure]
  (μN : letI := F.canonicalTopologicalData.topology;
    letI := borel (LeftUnipotentQuotient t F.Carrier);
    Measure (LeftUnipotentQuotient t F.Carrier))

/-- Determinant-slice integrals of the actual first-unfolding radical average.
The two supplied measures are retained. -/
def unfoldedJacquetSeries (f : TwoBlockJacquet.Sections F h σ)
    (Wtest : letI := F.canonicalTopologicalData.topology; WhittakerFunctions ψ t)
    (Φ : letI := F.canonicalTopologicalData.topology;
      SchwartzBruhat (Fin (t + 1) → F.Carrier)) : BilateralLaurentSeries :=
  letI := F.canonicalTopologicalData.topology
  letI : MeasurableSpace F.Carrier := borel F.Carrier
  sliceCoefficient F.canonicalTopologicalData μN
    (radicalAverage F h μR (TwoBlockUnfolding.integrand ell f Wtest Φ))

/-- The radical average is the actual equal-rank integrand associated to a
functional whose coefficients are the ordinary Jacquet integrals. -/
theorem radicalAverage_eq_equalRankIntegrand
    (J : letI := F.canonicalTopologicalData.topology;
      glInverseFunctionals ψ t (TwoBlockJacquet.inducedRep F h σ))
    (hJ : ∀ (f : TwoBlockJacquet.Sections F h σ)
      (g : GeneralLinear (t + 1) F.Carrier),
      J.val (TwoBlockJacquet.inducedRep F h σ g f) =
        TwoBlockJacquet.jacquetFunction ψ (fun i => (ell i).val) μR f g)
    (f : TwoBlockJacquet.Sections F h σ)
    (Wtest : letI := F.canonicalTopologicalData.topology; WhittakerFunctions ψ t)
    (Φ : letI := F.canonicalTopologicalData.topology;
      SchwartzBruhat (Fin (t + 1) → F.Carrier)) :
    letI := F.canonicalTopologicalData.topology
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    radicalAverage F h μR (TwoBlockUnfolding.integrand ell f Wtest Φ) =
      equalRankIntegrand ψ (normalizedAbsoluteValue F.canonicalTopologicalData)
        Wtest (modelMap (TwoBlockJacquet.inducedRep F h σ) J f).val Φ 0 := by
  let := F.canonicalTopologicalData.topology
  let : MeasurableSpace F.Carrier := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  funext q
  induction q using Quotient.inductionOn with
  | h g =>
    rw [TwoBlockUnfolding.radicalAverage_integrand_mk, equalRankIntegrand_zero_mk]
    change Wtest.val g * TwoBlockJacquet.jacquetFunction ψ
        (fun i => (ell i).val) μR f g * Φ (lastRow g) =
      Wtest.val g * J.val (TwoBlockJacquet.inducedRep F h σ g f) * Φ (lastRow g)
    rw [hJ]

/-- Identification of the unfolded coefficient series, without a convergence
premise. This is equality of total restricted Bochner integrals. -/
theorem unfoldedJacquetSeries_eq
    (J : letI := F.canonicalTopologicalData.topology;
      glInverseFunctionals ψ t (TwoBlockJacquet.inducedRep F h σ))
    (hJ : ∀ (f : TwoBlockJacquet.Sections F h σ)
      (g : GeneralLinear (t + 1) F.Carrier),
      J.val (TwoBlockJacquet.inducedRep F h σ g f) =
        TwoBlockJacquet.jacquetFunction ψ (fun i => (ell i).val) μR f g)
    (f : TwoBlockJacquet.Sections F h σ)
    (Wtest : letI := F.canonicalTopologicalData.topology; WhittakerFunctions ψ t)
    (Φ : letI := F.canonicalTopologicalData.topology;
      SchwartzBruhat (Fin (t + 1) → F.Carrier)) :
    unfoldedJacquetSeries F h ψ σ ell μR μN f Wtest Φ =
      equalRankSliceCoefficient F.canonicalTopologicalData μN ψ
        Wtest (modelMap (TwoBlockJacquet.inducedRep F h σ) J f).val Φ := by
  unfold unfoldedJacquetSeries equalRankSliceCoefficient
  rw [radicalAverage_eq_equalRankIntegrand F h ψ σ ell μR J hJ f Wtest Φ]

/-- Actual unfolded coefficients have a finite negative tail, once the supplied
ordinary Jacquet realization is identified. No uniform support bound is claimed. -/
theorem unfoldedJacquetSeries_lowerSupport
    (hσ : ∀ i, letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i))
    (J : letI := F.canonicalTopologicalData.topology;
      glInverseFunctionals ψ t (TwoBlockJacquet.inducedRep F h σ))
    (hJ : ∀ (f : TwoBlockJacquet.Sections F h σ)
      (g : GeneralLinear (t + 1) F.Carrier),
      J.val (TwoBlockJacquet.inducedRep F h σ g f) =
        TwoBlockJacquet.jacquetFunction ψ (fun i => (ell i).val) μR f g) :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    letI := F.canonicalTopologicalData.localField
    letI := borel (GeneralLinear (t + 1) F.Carrier)
    letI : BorelSpace (GeneralLinear (t + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent (t + 1) F.Carrier)
    letI : BorelSpace (upperUnipotent (t + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient t F.Carrier)
    letI : BorelSpace (LeftUnipotentQuotient t F.Carrier) := ⟨rfl⟩
    ∀ [Measure.IsMulRightInvariant (unipotentHaar F.Carrier t)],
      IsCompatible (upperUnipotent (t + 1) F.Carrier)
        (generalLinearHaar F.Carrier t) (unipotentHaar F.Carrier t) μN →
      ∀ {V : Type uV} [AddCommGroup V] [Module ℂ V]
        (π : Representation ℂ (GeneralLinear (t + 1) F.Carrier) V),
        IsOfWhittakerType t (standardCharacter ψ t) π →
        ∀ (lambda : glFunctionals ψ t π)
          (Wtest : (coefficientModel π lambda).toSubmodule)
          (f : TwoBlockJacquet.Sections F h σ)
          (Φ : SchwartzBruhat (Fin (t + 1) → F.Carrier)),
          BilateralLaurentSeries.HasLowerBoundedSupport
            (unfoldedJacquetSeries F h ψ σ ell μR μN f Wtest.val Φ) := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := borel (GeneralLinear (t + 1) F.Carrier)
  let : BorelSpace (GeneralLinear (t + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (t + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (t + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient t F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient t F.Carrier) := ⟨rfl⟩
  intro _ hμ V _ _ π hπ lambda Wtest f Φ
  rw [unfoldedJacquetSeries_eq F h ψ σ ell μR μN J hJ f Wtest.val Φ]
  exact equalRankSliceSupport F F.canonicalTopologicalData t ψ μN hμ V
    (TwoBlockJacquet.Sections F h σ) π (TwoBlockJacquet.inducedRep F h σ) hπ
    (lowerInduced_inverseWhittakerType F h ψ σ hσ) lambda J Wtest
    (modelMap (TwoBlockJacquet.inducedRep F h σ) J f) Φ

end Series

section Family

local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance : SecondCountableTopology F.Carrier := F.canonicalTopologicalData.secondCountableTopology
local instance : MeasurableSpace F.Carrier := borel F.Carrier
local instance : BorelSpace F.Carrier := ⟨rfl⟩
local instance : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance : MeasurableSpace (GeneralLinear (t + 1) F.Carrier) :=
  borel (GeneralLinear (t + 1) F.Carrier)
local instance : BorelSpace (GeneralLinear (t + 1) F.Carrier) := ⟨rfl⟩
local instance : MeasurableSpace (upperUnipotent (t + 1) F.Carrier) :=
  borel (upperUnipotent (t + 1) F.Carrier)
local instance : BorelSpace (upperUnipotent (t + 1) F.Carrier) := ⟨rfl⟩
local instance : MeasurableSpace (LeftUnipotentQuotient t F.Carrier) :=
  borel (LeftUnipotentQuotient t F.Carrier)
local instance : BorelSpace (LeftUnipotentQuotient t F.Carrier) := ⟨rfl⟩

/-- Above one ordinary convergence bound, the actual unfolded series are
coefficient series with lower-bounded support, for every compatible quotient
measure, test representation, coefficient, section and row test. -/
theorem exists_supported_unfoldedJacquetSeries
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (τ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i))
    (hτ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (τ i))
    (ell0 : ∀ i, glInverseFunctionals ψ (m i) (τ i))
    (hell0 : ∀ i, (ell0 i).val ≠ 0) :
    ∃ C : ℝ, ∀ u : ℝ, C < u →
      let σ := twoBlockOppositeTwistBlocks F m τ u
      let ell := fun i => twoBlockOppositeTwistFunctional F m ψ τ u i (ell0 i)
      let μR := rectangularMeasure ν.val (m 0 + 1) (m 1 + 1)
      (∀ f : TwoBlockJacquet.Sections F h σ,
        TwoBlockJacquet.IsAbsIntegrable ψ (fun i => (ell0 i).val) μR f) ∧
      ∃ J : glInverseFunctionals ψ t (TwoBlockJacquet.inducedRep F h σ),
        J.val ≠ 0 ∧
        (∀ (f : TwoBlockJacquet.Sections F h σ) (g : GeneralLinear (t + 1) F.Carrier),
          J.val (TwoBlockJacquet.inducedRep F h σ g f) =
            TwoBlockJacquet.jacquetFunction ψ (fun i => (ell0 i).val) μR f g) ∧
        ∀ [Measure.IsMulRightInvariant (unipotentHaar F.Carrier t)]
          (μN : Measure (LeftUnipotentQuotient t F.Carrier)),
          IsCompatible (upperUnipotent (t + 1) F.Carrier)
            (generalLinearHaar F.Carrier t) (unipotentHaar F.Carrier t) μN →
          ∀ {V : Type uV} [AddCommGroup V] [Module ℂ V]
            (π : Representation ℂ (GeneralLinear (t + 1) F.Carrier) V),
            IsOfWhittakerType t (standardCharacter ψ t) π →
            ∀ (lambda : glFunctionals ψ t π)
              (Wtest : (coefficientModel π lambda).toSubmodule)
              (f : TwoBlockJacquet.Sections F h σ)
              (Φ : SchwartzBruhat (Fin (t + 1) → F.Carrier)),
              unfoldedJacquetSeries F h ψ σ ell μR μN f Wtest.val Φ =
                equalRankSliceCoefficient F.canonicalTopologicalData μN ψ
                  Wtest.val (modelMap (TwoBlockJacquet.inducedRep F h σ) J f).val Φ ∧
              BilateralLaurentSeries.HasLowerBoundedSupport
                (unfoldedJacquetSeries F h ψ σ ell μR μN f Wtest.val Φ) := by
  obtain ⟨C, hC⟩ := twoBlockOrdinaryJacquetFunctional p F ψ ν t m h τ hτ ell0 hell0
  refine ⟨C, fun u hu => ?_⟩
  obtain ⟨habs, J, hJ0, hJ⟩ := hC u hu
  refine ⟨habs, J, hJ0, hJ, ?_⟩
  intro _ μN hμ V _ _ π hπ lambda Wtest f Φ
  have hσ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i))
      (twoBlockOppositeTwistBlocks F m τ u i) := fun i =>
    (twoBlockOppositeTwistBlocks_isOfWhittakerType_iff F m τ u i _).2 (hτ i)
  let σ := twoBlockOppositeTwistBlocks F m τ u
  let ell := fun i => twoBlockOppositeTwistFunctional F m ψ τ u i (ell0 i)
  let μR := rectangularMeasure ν.val (m 0 + 1) (m 1 + 1)
  exact ⟨unfoldedJacquetSeries_eq F h ψ σ ell μR μN J hJ f Wtest.val Φ,
    unfoldedJacquetSeries_lowerSupport F h ψ σ ell μR μN hσ J hJ hμ
      π hπ lambda Wtest f Φ⟩

end Family

end Langlands.RankinSelberg.DominantRankTransport
