import Langlands.Algebra.NonUnitalModuleDualLeftExactnessProof
import Langlands.Algebra.NonUnitalModuleDualRightExactnessProof

/-! Exactness of both actual contravariant nondegenerate dual functors. -/

set_option autoImplicit false

noncomputable section

namespace Langlands.Algebra

universe uA uM

open NonUnitalModuleDual

/-- The unchanged closed categorical target, including both actual orientations. -/
theorem nonUnitalModuleDualCategoricalExactnessStatement :
    NonUnitalModuleDualCategoricalExactnessStatement.{uA, uM} := by
  intro A _ _ _ _ hA
  let _ := NondegenerateModuleCat.abelian.{uA, uM} A hA
  let _ := NondegenerateModuleCat.abelian.{uA, uM} Aᵐᵒᵖ hA.op
  refine ⟨leftToRight_additive hA, rightToLeft_additive hA, ?_⟩
  exact ⟨leftToRight_sequenceExact hA, rightToLeft_sequenceExact hA,
    leftToRight_exact hA, leftToRight_shortExact hA,
    rightToLeft_exact hA, rightToLeft_shortExact hA⟩

example : NonUnitalModuleDualCategoricalExactnessStatement.{uA, uM} :=
  @nonUnitalModuleDualCategoricalExactnessStatement.{uA, uM}

example : NonUnitalModuleDualCategoricalExactnessStatement.{0, 1} :=
  @nonUnitalModuleDualCategoricalExactnessStatement.{0, 1}

example : NonUnitalModuleDualCategoricalExactnessStatement.{1, 0} :=
  @nonUnitalModuleDualCategoricalExactnessStatement.{1, 0}

end Langlands.Algebra
