import Langlands.Global.RankinSelberg.ArchimedeanCentralSignProof
import Langlands.Global.RankinSelberg.ArchimedeanOrdinaryTestsFromGeneration
import Langlands.Global.RankinSelberg.ComplexPlaceWhittakerRange
import Langlands.Global.RankinSelberg.EqualSemilocalFactorizationReductionTC
import Langlands.Global.RankinSelberg.InfiniteWhittakerActualRanges
import Langlands.Global.RankinSelberg.InfiniteWhittakerComplexSliceData
import Langlands.Global.RankinSelberg.SchwartzBruhatProof.Duality
import Langlands.Global.RankinSelberg.UnipotentClassProductProof

/-! # The equal-rank semi-local equation from ordinary tests at complex places -/

noncomputable section

set_option autoImplicit false

universe u uQ

namespace Langlands.Global.RankinSelbergGlobal

open NumberField Langlands.Automorphic Langlands.Global.CuspidalPairFunctionalEquation
open Langlands.Global.HeckeFunctionalEquation
open Langlands.ClassFieldTheory.Global.RelativeWeilGroup
open scoped CategoryTheory.MonObj

/-- The normalized complex slice data supply the single-representation model at a
specified totally complex field. -/
theorem infiniteWhittakerSliceModelAt_of_isTotallyComplex (F : Type u)
    [Field F] [NumberField F] [IsTotallyComplex F] [CompactSpace (AdeleQuotient F)] :
    InfiniteWhittakerSliceModelAt.{u, uQ} F := by
  classical
  intro r T P hP χ hχ _ _ dC hdC
  let ψ := SchwartzBruhatProof.standardUnitary χ hχ
  have hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1 :=
    SchwartzBruhatProof.standardUnitary_diagonal χ hχ
  choose aC haC using exists_isComplexAdditiveComponent ψ hψ
  obtain ⟨M, -⟩ := infiniteWhittakerComplexSliceData F ψ hψ r T P hP aC haC dC hdC
  have heq : ψ.complex = χ := DFunLike.ext _ _ fun _ => rfl
  rw [heq] at M
  exact ⟨M⟩

/-- Ordinary local equal-rank tests at complex places in ranks `r+1` with `0 < r`
suffice for pointwise factorization at a totally complex field. -/
theorem equalPointwiseFactorizationTC_of_ordinaryTests
    (hOrd : ComplexEqualOrdinaryPlaceTestsPositiveRankStatement.{u}) :
    EqualPointwiseFactorizationTCStatement.{u, uQ} := by
  intro F _ _ _ _
  have hReal (hv : Nonempty {v : InfinitePlace F // v.IsReal}) : False := by
    rcases hv with ⟨v⟩
    exact InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex v.1) v.2
  exact equalPointwiseAtOfInfiniteTests F
    (equalInfiniteWhittakerTestAt_of_local F (infiniteWhittakerSliceModelAt_of_isTotallyComplex F)
      (fun hv => (hReal hv).elim)
      (complexEqualPlaceTests_of_positive (complexEqualPlaceTestsPositiveRank_of_ordinary hOrd)))

/-- Ordinary nonvanishing at complex places in ranks `r+1` with `0 < r` implies the
totally complex equal-rank semi-local equation. -/
def EqualSemilocalEquationTCFromOrdinaryTestsStatement : Prop :=
  ComplexEqualOrdinaryPlaceTestsPositiveRankStatement.{u} →
  EqualSemilocalEquationTCStatement.{u, uQ}

theorem equalSemilocalEquationTCFromOrdinaryTests :
    EqualSemilocalEquationTCFromOrdinaryTestsStatement.{u, uQ} := by
  intro hOrd
  have hPoint := equalPointwiseFactorizationTC_of_ordinaryTests.{u, uQ} hOrd
  have hFact : EqualArchimedeanFactorizationTCStatement.{u, uQ} := fun F _ _ _ _ =>
    equalArchimedeanFactorizationAt_of_pointwise F (hPoint F)
      UnipotentClass.unipotentClassProductStatement
  exact equalSemilocalReductionTC (equalSemilocalFactorizationTC_of_factorizationTC
    complexPlaceFunctionalEquation.2 hFact archimedeanCentralSign)

private theorem complexWhittakerRestrictionOnto :
    ComplexPlaceWhittakerRestrictionOntoStatement.{u} := by
  classical
  intro F _ _ _ ψ hψ r T w a ha d hd W
  constructor
  · intro hW
    obtain ⟨x, hx⟩ := complexPlaceWhittakerRange F ψ hψ r T w d hd a ha W hW
    exact ⟨x, 1, funext fun g => by rw [InfiniteWhittakerSlice.finitePoint_one, mul_one, hx g]⟩
  · intro hW
    let ψ' := inverseCharacter ψ
    have ha' : IsComplexAdditiveComponent ψ' w.1 w.2 (-a) := by
      intro y
      apply Subtype.ext
      change ψ'.complex (((Pi.single w.1 y : InfiniteAdeles F), (0 : FiniteAdeles F)) : Adeles F) = _
      rw [show ψ'.complex = ψ.complex⁻¹ from complex_inverseCharacter ψ]
      exact complexComponent_complex_inv ψ w a ha y
    obtain ⟨x, hx⟩ := complexPlaceWhittakerRange F ψ' (inverseCharacter_rational ψ hψ) r T w d hd
      (-a) ha' W hW
    refine ⟨x, 1, funext fun g => ?_⟩
    rw [InfiniteWhittakerSlice.finitePoint_one, mul_one]
    simpa only [ψ', complex_inverseCharacter] using hx g

/-- The complex ordinary normalized generation theorem supplies the ordinary tests.
Only its equal-rank coverage is used. -/
theorem equalSemilocalEquationTC_of_ordinaryGeneration
    (hGen : ComplexOrdinaryNormalizedGenerationStatement) : EqualSemilocalEquationTCStatement.{u, uQ} :=
  equalSemilocalEquationTCFromOrdinaryTests
    (complexOrdinaryPlaceTests_of_generation hGen complexWhittakerRestrictionOnto).2

end Langlands.Global.RankinSelbergGlobal
