import Langlands.Algebra.NonUnitalModuleDualMapExactnessProof

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra

universe uA uM uN

/-- The closed endpoint target retains independent algebra/source/target universes. -/
theorem nonUnitalModuleDualInjectiveSurjectiveStatement :
    NonUnitalModuleDualInjectiveSurjectiveStatement.{uA, uM, uN} := by
  intro A _ _ _ _ hA M _ _ N _ _ hM hN f
  exact NonUnitalModuleDual.pullback_surjective_of_injective hA hM hN f

example : NonUnitalModuleDualInjectiveSurjectiveStatement.{uA, uM, uN} :=
  @nonUnitalModuleDualInjectiveSurjectiveStatement.{uA, uM, uN}

example : NonUnitalModuleDualInjectiveSurjectiveStatement.{0, 1, 2} :=
  @nonUnitalModuleDualInjectiveSurjectiveStatement.{0, 1, 2}

example : NonUnitalModuleDualInjectiveSurjectiveStatement.{2, 0, 1} :=
  @nonUnitalModuleDualInjectiveSurjectiveStatement.{2, 0, 1}

example : NonUnitalModuleDualInjectiveSurjectiveStatement.{1, 2, 0} :=
  @nonUnitalModuleDualInjectiveSurjectiveStatement.{1, 2, 0}

end Langlands.Algebra
