import Langlands.Automorphic.CuspidalWhittakerSmoothBound
import Langlands.Automorphic.CuspidalOperatorUnitaryMultiplicityOneReduction

/-! # Actual cuspidal multiplicity one from band estimates and comparison -/

noncomputable section

universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped CategoryTheory.MonObj

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.RankinSelbergGlobal MeasureTheory

/-- The actual fixed-level Whittaker band derivative estimate for every
unitary-center cuspidal realization and standard additive character. -/
def CuspidalWhittakerBandBoundStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] (r : ℕ)
    (T : CuspidalOperatorRealization F r),
    Langlands.ClassFieldTheory.Global.RelativeWeilGroup.HasUnitaryCentralCharacter T →
    ∀ (hL2 : ∀ x : T.Space,
        MemLp (OperatorDeterminantSlice.toQuotient F (r + 1) T.realization x) 2
          ((OperatorDeterminantSlice.quotientHaarMeasure F (r + 1)).restrict
            (OperatorDeterminantSlice.band F (r + 1))))
      (ψ : AddChar (Adeles F) ℂ), IsStandardAdditiveCharacter F ψ →
      CuspidalWhittakerBandBound F T hL2 ψ

/-- The remaining analytic comparison input, restricted to actual
unitary-center cuspidal realizations with the actual band derivative bounds.
It still requires one scalar uniform over the original vector and group point. -/
def CuspidalWhittakerBandSobolevComparisonStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] (r : ℕ)
    (T T' : CuspidalOperatorRealization F r),
    Langlands.ClassFieldTheory.Global.RelativeWeilGroup.HasUnitaryCentralCharacter T →
    Langlands.ClassFieldTheory.Global.RelativeWeilGroup.HasUnitaryCentralCharacter T' →
    ∀ (e : T.Equivalence T') (ψ : AddChar (Adeles F) ℂ),
      IsStandardAdditiveCharacter F ψ →
      ∀ (hL2 : ∀ x : T.Space,
          MemLp (OperatorDeterminantSlice.toQuotient F (r + 1) T.realization x) 2
            ((OperatorDeterminantSlice.quotientHaarMeasure F (r + 1)).restrict
              (OperatorDeterminantSlice.band F (r + 1))))
        (hL2' : ∀ x : T'.Space,
          MemLp (OperatorDeterminantSlice.toQuotient F (r + 1) T'.realization x) 2
            ((OperatorDeterminantSlice.quotientHaarMeasure F (r + 1)).restrict
              (OperatorDeterminantSlice.band F (r + 1)))),
        CuspidalWhittakerBandBound F T hL2 ψ →
        CuspidalWhittakerBandBound F T' hL2' ψ →
        ∃ c : ℂ, ∀ (v : T.Space) (g : Points F (r + 1)),
          cuspWhittaker F T' ψ (e v) g = c * cuspWhittaker F T ψ v g

/-- The exact unrestricted multiplicity-one consequent, retaining the actual
band estimate and analytic comparison as two named open premises. -/
def CuspidalWhittakerBandReductionStatement : Prop :=
  CuspidalWhittakerBandBoundStatement.{u} →
    CuspidalWhittakerBandSobolevComparisonStatement.{u} →
      CuspidalOperatorMultiplicityOneStatement.{u}

set_option maxHeartbeats 1600000 in
/-- Normalize to unitary central characters, apply the retained band estimate
and analytic comparison, and reconstruct the actual realization. -/
theorem cuspidalWhittakerBandReduction :
    CuspidalWhittakerBandReductionStatement.{u} := by
  intro hBand hComparison
  apply cuspidalOperatorUnitaryMultiplicityOneReduction
  intro F _ _ _ r T T' hT hT' ⟨e⟩
  let ψ := EqualAnalytic.standardCharacter F
  have hψ : IsStandardAdditiveCharacter F ψ := by
    refine ⟨EqualAnalytic.continuous_standardCharacter F, ?_,
      EqualAnalytic.standardCharacter_algebraMap F, ?_⟩
    · obtain ⟨x, hx⟩ := CuspidalWhittaker.exists_adelicCharacter_ne_one F
      intro hh
      apply hx
      apply (EqualAnalytic.standardCharacter_eq_one_iff F x).mp
      exact congrArg (fun χ : AddChar (Adeles F) ℂ => χ x) hh
    · intro x
      exact Circle.norm_coe _
  let hL2 := memLp_cuspidal_toQuotient_band F T
  let hL2' := memLp_cuspidal_toQuotient_band F T'
  have hb := hBand F r T hT hL2 ψ hψ
  have hb' := hBand F r T' hT' hL2' ψ hψ
  obtain ⟨c, hc⟩ := hComparison F r T T' hT hT' e ψ hψ hL2 hL2' hb hb'
  exact CuspidalMultiplicityOne.realization_eq_of_whittaker_comparison F T T' e ψ hψ c hc


end Langlands.Automorphic
