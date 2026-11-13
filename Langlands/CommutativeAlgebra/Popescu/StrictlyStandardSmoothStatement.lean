import Langlands.CommutativeAlgebra.Popescu.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Smooth.Basic

/-! # Inverting a strictly standard element gives a smooth algebra -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

/-- Stacks Lemma 16.3.7 (07EZ), part (d): if `a` is strictly standard in `A` over `R`,
then `A_a` is smooth over `R`. -/
def StrictlyStandardSmoothStatement : Prop :=
  ∀ (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] (a : A),
    IsStrictlyStandard R a → Algebra.Smooth R (Localization.Away a)

end Langlands.CommutativeAlgebra.Popescu
