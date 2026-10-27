import Mathlib.CategoryTheory.Action.Continuous

/-! # The identity forgetful functor for continuous topological actions -/

universe u

open CategoryTheory

namespace Langlands.Analytic.NormContinuousAffinoidAction

/-- The identity forgetful functor, used explicitly for Mathlib's continuous
actions on `TopCat` itself. It is not registered as a global instance. -/
@[instance_reducible]
def topCatSelfForget : HasForget₂ TopCat.{u} TopCat.{u} where
  forget₂ := 𝟭 _
  forget_comp := rfl

end Langlands.Analytic.NormContinuousAffinoidAction
