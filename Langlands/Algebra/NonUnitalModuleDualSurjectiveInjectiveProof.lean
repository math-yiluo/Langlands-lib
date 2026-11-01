import Langlands.Algebra.NonUnitalModuleDualMapExactnessProof

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra

universe uA uM uN

/-- The closed endpoint target retains independent algebra/source/target universes. -/
theorem nonUnitalModuleDualSurjectiveInjectiveStatement :
    NonUnitalModuleDualSurjectiveInjectiveStatement.{uA, uM, uN} := by
  intro A _ _ _ _ hA M _ _ N _ _ hM hN f
  exact NonUnitalModuleDual.pullback_injective_of_surjective hA hM hN f

example : NonUnitalModuleDualSurjectiveInjectiveStatement.{uA, uM, uN} :=
  @nonUnitalModuleDualSurjectiveInjectiveStatement.{uA, uM, uN}

example : NonUnitalModuleDualSurjectiveInjectiveStatement.{0, 1, 2} :=
  @nonUnitalModuleDualSurjectiveInjectiveStatement.{0, 1, 2}

example : NonUnitalModuleDualSurjectiveInjectiveStatement.{2, 0, 1} :=
  @nonUnitalModuleDualSurjectiveInjectiveStatement.{2, 0, 1}

example : NonUnitalModuleDualSurjectiveInjectiveStatement.{1, 2, 0} :=
  @nonUnitalModuleDualSurjectiveInjectiveStatement.{1, 2, 0}

end Langlands.Algebra
