import Langlands.Algebra.NonUnitalModuleFreeCounterexampleStatements
import Langlands.Algebra.CountableLocalUnitsObstruction

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace Langlands.Algebra.NonUnitalModuleFreeCounterexampleProof

universe uR uX uL

/-- The actual countable-support regular module is nonprojective, free, and a free direct factor. -/
theorem generalCounterexamples :
    NonUnitalModuleFreeCounterexampleStatements.GeneralCounterexamplesStatement.{uR, uX, uL} := by
  intro R _ _ X _
  let A := CountableSupportAlgebra.Carrier R X
  let hA : IsIdempotented A := CountableSupportAlgebra.isIdempotented
  let := NondegenerateModuleCat.abelian.{max uR uX, max (max uR uX) uL} A hA
  let P := NonUnitalModuleFree.regularObject.{max uR uX, uL} hA
  have hcount (a : ℕ → A) : ∃ e : A, ∀ n, a n * e = a n := by
    obtain ⟨e, he⟩ := CountableSupportAlgebra.countable_local_units a
    exact ⟨(e : A), fun n => (he n).2⟩
  have hno : ¬ ∃ e : A, ∀ a : A, a * e = a := by
    rintro ⟨e, he⟩
    apply CountableSupportAlgebra.no_left_identity (R := R) (X := X)
    exact ⟨e, fun a => (mul_comm e a).trans (he a)⟩
  have hnp : ¬ Langlands.Renard.HomProjective P := by
    intro hp
    exact CountableLocalUnitsObstruction.regular_not_projective hA hcount hno
      ((Langlands.Renard.homProjectiveComparison P).mp hp)
  refine ⟨CountableLocalUnitsObstruction.regular_isFree hA, hnp, ?_⟩
  refine ⟨PUnit.{max (max uR uX) uL + 1}, 0, ⟨?_⟩⟩
  exact (CountableLocalUnitsObstruction.regularSingleIso hA PUnit).symm ≪≫
    isoBiprodZero (isZero_zero (NondegenerateModuleCat.{max uR uX, max (max uR uX) uL} A))

/-- The specialization to actual complex-valued functions on the complex numbers. -/
theorem complexCounterexample :
    NonUnitalModuleFreeCounterexampleStatements.ComplexCounterexampleStatement.{uL} := by
  let : Uncountable ℂ := Set.not_countable_univ_iff.mp not_countable_complex
  exact generalCounterexamples.{0, 0, uL} ℂ ℂ

/-- The exact closed aggregate of the general and complex counterexamples. -/
theorem freeCounterexampleAssertions :
    NonUnitalModuleFreeCounterexampleStatements.FreeCounterexampleAssertions.{uR, uX, uL} :=
  ⟨generalCounterexamples, complexCounterexample⟩

end Langlands.Algebra.NonUnitalModuleFreeCounterexampleProof
