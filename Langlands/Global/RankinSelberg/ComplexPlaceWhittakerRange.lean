import Langlands.Global.RankinSelberg.ArchimedeanActualWhittakerIntertwiners
import Langlands.Global.RankinSelberg.ComplexJacquetMultiplicityOne

/-! # Realizing the full specified Whittaker model at a complex place -/

noncomputable section

universe u

open NumberField
open scoped Classical CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal

open Automorphic HeckeFunctionalEquation LocalFactor.Archimedean

/-- Every function in the specified complex Whittaker model of an actual cuspidal
realization is its adelic Whittaker restriction with finite coordinate one. -/
def ComplexPlaceWhittakerRangeStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)),
    (∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) →
  ∀ (r : ℕ) (T : CuspidalOperatorRealization F r)
    (w : {v : InfinitePlace F // v.IsComplex}) (d : List ComplexCharacterData),
    T.realization.HasComplexPlaceParameter w d →
  ∀ (a : ℂˣ), IsComplexAdditiveComponent ψ w.1 w.2 a →
  ∀ W : GeneralLinear (r + 1) ℂ → ℂ, W ∈ complexWhittakerModel r d a →
    ∃ x : T.Space, ∀ g, W g = cuspWhittaker F T ψ.complex x (complexPlacePoint F (r + 1) w g)

theorem complexPlaceWhittakerRange : ComplexPlaceWhittakerRangeStatement.{u} := by
  intro F _ _ _ ψ hψ r T w d hd a ha W hW
  obtain ⟨A, B, _, hB, ⟨f₀, hf₀⟩, hVal⟩ :=
    (archimedeanActualWhittakerIntertwiners F ψ hψ r T).2 w d hd a ha
  have hNonzero : B ≠ 0 := by
    intro h
    rw [h] at hf₀
    exact zero_ne_one hf₀
  rw [ComplexJacquetMultiplicityOne.model_eq_range_of_nonzero r d a B hB hNonzero] at hW
  obtain ⟨f, rfl⟩ := hW
  exact ⟨A f, hVal f⟩

end Langlands.Global.RankinSelbergGlobal
