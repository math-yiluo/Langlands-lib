import Langlands.Global.RankinSelberg.ArchimedeanQuotientMeasures
import Langlands.Global.RankinSelberg.ArchimedeanWhittakerIdentityEvaluation
import Langlands.Global.RankinSelberg.ComplexPlaceEqualFunctionalEquationProof
import Langlands.Global.RankinSelberg.ComplexPlaceFunctionalEquationLocalFEReduction
import Langlands.Global.RankinSelberg.ComplexPlaceWhittakerRange
import Langlands.Global.RankinSelberg.ComplexUnequalRankOneOrdinary
import Langlands.Global.RankinSelberg.UnequalInfiniteWhittakerSliceReduction
import Langlands.Global.RankinSelberg.UnequalPlaceTestsFromOrdinary

/-! # Pointwise factorization from the slice comparison and archimedean tests -/

noncomputable section

open NumberField
open scoped Classical CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u uQ

namespace Langlands.Global.RankinSelbergGlobal

open Automorphic ArchimedeanLocal HeckeFunctionalEquation LocalFactor.Archimedean

/-- Some actual pair of opposite-character restrictions has a nonzero ordinary integral
arbitrarily far to the right when the smaller representation is on `GL₁(ℂ)`. -/
theorem complexUnequalOrdinaryPlaceTest_rankOne
    {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F))
    (hψ : ∀ x : F, ψ (algebraMap F (Adeles F) x) = 1)
    {r : ℕ} (h : 0 < r) (T : CuspidalOperatorRealization F r)
    (T' : CuspidalOperatorRealization F 0) (w : {v : InfinitePlace F // v.IsComplex}) (a : ℂˣ)
    (ha : IsComplexAdditiveComponent ψ w.1 w.2 a) (d e : List ComplexCharacterData)
    (hd : T.realization.HasComplexPlaceParameter w d) (he : T'.realization.HasComplexPlaceParameter w e) :
    ∃ (W : GeneralLinear (r + 1) ℂ → ℂ) (V : GeneralLinear 1 ℂ → ℂ) (D : ComplexQuotientMeasureData 0),
      IsComplexPlaceWhittaker F T ψ.complex w W ∧ IsComplexPlaceWhittaker F T' ψ.complex⁻¹ w V ∧
      ∀ b : ℝ, ∃ s : ℂ, b < s.re ∧ complexUnequalIntegral h D W V s ≠ 0 := by
  obtain ⟨_, B, _, hB, ⟨v, hv⟩, _⟩ :=
    (archimedeanActualWhittakerIntertwiners F ψ hψ r T).2 w d hd a ha
  have hχ := UnramifiedWhittaker.isStandardAdditiveCharacter_complex F ψ hψ
  have hχ' := Unfolding.isStandardAdditiveCharacter_inv F ψ.complex hχ
  obtain ⟨V, hV, hV₁⟩ :=
    ArchimedeanWhittakerEvaluation.exists_complexPlaceWhittaker_one_ne_zero T' ψ.complex⁻¹ hχ' w
  let V' : complexWhittakerModel 0 e (-a) :=
    ⟨V, ((complexPlaceWhittakerModelReduction
      (complexPlaceWhittakerIntertwinerReduction complexPlaceWhittakerAnalytic))
        F ψ hψ 0 T' w a ha e he V).2 hV⟩
  let D := complexQuotientMeasureData 0
  obtain ⟨U, hU⟩ := ComplexUnequalRankOne.exists_complexUnequalIntegral_rankOne_ne_zero_above
    h hd.1 he.1 a D B hB v V' (by rw [hv]; exact one_ne_zero) hV₁
  obtain ⟨x, hx⟩ := complexPlaceWhittakerRange F ψ hψ r T w d hd a ha U.val U.2
  refine ⟨U.val, V, D, ⟨x, 1, ?_⟩, hV, hU⟩
  funext g
  simpa only [finitePoint, map_one, ArchimedeanWhittakerEvaluation.adelicPoint_one, mul_one] using hx g

/-- Ordinary complex-place test existence when the smaller group has rank at least two. -/
def ComplexUnequalOrdinaryPlaceTestsPositiveRankStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
    (∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) →
  ∀ (r t : ℕ) (h : t < r), 0 < t →
  ∀ (T : CuspidalOperatorRealization F r) (T' : CuspidalOperatorRealization F t)
    (w : {v : InfinitePlace F // v.IsComplex}) (a : ℂˣ),
    IsComplexAdditiveComponent ψ w.1 w.2 a →
  ∀ (d e : List ComplexCharacterData),
    T.realization.HasComplexPlaceParameter w d → T'.realization.HasComplexPlaceParameter w e →
    ∃ (W : GeneralLinear (r + 1) ℂ → ℂ) (V : GeneralLinear (t + 1) ℂ → ℂ)
      (D : ComplexQuotientMeasureData t),
      IsComplexPlaceWhittaker F T ψ.complex w W ∧ IsComplexPlaceWhittaker F T' ψ.complex⁻¹ w V ∧
      ∀ b : ℝ, ∃ s : ℂ, b < s.re ∧ complexUnequalIntegral h D W V s ≠ 0

/-- The ordinary complex-place tests follow from the clause with smaller rank at least two. -/
theorem complexUnequalOrdinaryPlaceTests_of_positiveRank
    (hpos : ComplexUnequalOrdinaryPlaceTestsPositiveRankStatement.{u}) :
    ComplexUnequalOrdinaryPlaceTestsStatement.{u} := by
  intro F _ _ _ ψ hψ r t h T T' w a ha d e hd he
  rcases t with _ | t
  · exact complexUnequalOrdinaryPlaceTest_rankOne ψ hψ h T T' w a ha d e hd he
  · exact hpos F ψ hψ r (t + 1) h t.succ_pos T T' w a ha d e hd he

/-- The exact global pointwise factorization follows from the slice comparison, the real-place
joint tests and the ordinary complex-place tests with smaller rank at least two. -/
def UnequalPointwiseFactorizationFromOrdinaryStatement : Prop :=
  InfiniteWhittakerSliceModelStatement.{u, uQ} →
    RealUnequalPlaceTestsStatement.{u} →
    ComplexUnequalOrdinaryPlaceTestsPositiveRankStatement.{u} →
    UnequalPointwiseFactorizationStatement.{u, uQ}

theorem unequalPointwiseFactorizationFromOrdinary :
    UnequalPointwiseFactorizationFromOrdinaryStatement.{u, uQ} := by
  intro hModels hReal hComplex
  have hFE := (complexPlaceFunctionalEquationLocalFEReduction.{u}
    complexLocalUnequalFunctionalEquation complexLocalEqualFunctionalEquation).1
  exact unequalInfiniteWhittakerSliceReduction hModels hReal
    (complexUnequalPlaceTests_of_ordinary hFE (complexUnequalOrdinaryPlaceTests_of_positiveRank hComplex))

end Langlands.Global.RankinSelbergGlobal
