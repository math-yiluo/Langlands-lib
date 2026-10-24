import Langlands.Automorphic.CenterFinite
import Langlands.Automorphic.FiniteVectors
import Langlands.Global.ArchimedeanCenterFinite

/-! # Transport of adelic finiteness to actual smooth infinite slices -/

noncomputable section
universe u
set_option autoImplicit false

namespace Langlands.Automorphic

open Langlands.Global

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- Evaluation of a simultaneously center-finite family is center finite. -/
def CenterFiniteFamilyEvaluationStatement : Prop :=
  ∀ F : SmoothSliceFamily K n, IsCenterFiniteFamily K n F →
    ∀ b : FiniteAdelicGL K n, ArchimedeanGL.IsCenterFinite K n (F b)

/-- The actual smooth slice of an infinite-subgroup-finite adelic function
is finite under that subgroup's smooth right action. -/
def SmoothSliceSubgroupFiniteStatement : Prop :=
  ∀ (U : Subgroup (InfiniteAdelicGL K n)) (f : SmoothRationalFunctions K n),
    IsInfiniteFinite K n U f.val →
      ∀ b : FiniteAdelicGL K n, Langlands.FiniteVectors.IsFiniteVector
        ((ArchimedeanGL.smoothRightAction K n).comp U.subtype)
        (smoothInfiniteSlice K n b f)

/-- Both algebraic finiteness transports needed at each automorphic slice. -/
def SliceFinitenessStatement : Prop :=
  CenterFiniteFamilyEvaluationStatement K n ∧ SmoothSliceSubgroupFiniteStatement K n

example : (K : Type u) → [Field K] → [NumberField K] → ℕ → Prop :=
  @SliceFinitenessStatement

end Langlands.Automorphic
