import Langlands.Automorphic.Forms
import Langlands.Global.ArchimedeanJointFinite

/-! # Joint differential finiteness of actual automorphic slices -/

noncomputable section
universe u
set_option autoImplicit false

namespace Langlands.Automorphic

open Langlands.Global

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- Every actual infinite slice of an automorphic form has finite joint orbit
under the genuine center and compact enveloping actions. -/
def AutomorphicSliceJointFiniteStatement : Prop :=
  ∀ f : SmoothRationalFunctions K n, IsAutomorphicForm K n f →
    ∀ b : FiniteAdelicGL K n,
      ArchimedeanGL.IsJointFinite K n (smoothInfiniteSlice K n b f)

example : (K : Type u) → [Field K] → [NumberField K] → ℕ → Prop :=
  @AutomorphicSliceJointFiniteStatement

end Langlands.Automorphic
