import Langlands.Automorphic.SliceJointFiniteStatement
import Langlands.Automorphic.SliceFinitenessProof
import Langlands.Global.ArchimedeanCompactGroupFiniteProof
import Langlands.Global.ArchimedeanSeparateJointFiniteProof

/-! # Joint differential finiteness of actual automorphic slices -/

noncomputable section
universe u
set_option autoImplicit false

namespace Langlands.Automorphic

open Langlands.Global

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- The actual compact and simultaneous center conditions give each slice a
finite joint orbit under the genuine center and compact enveloping actions. -/
theorem automorphicSliceJointFinite : AutomorphicSliceJointFiniteStatement K n := by
  intro f hf b
  have hc : ArchimedeanGL.IsCenterFinite K n (smoothInfiniteSlice K n b f) :=
    (SliceFinitenessProof.sliceFiniteness K n).1 (smoothSliceFamily K n f) hf.2.2.1 b
  have hk := (SliceFinitenessProof.sliceFiniteness K n).2
    (standardInfiniteCompact K n) f hf.2.1 b
  exact ArchimedeanGL.separateJointFinite K n (smoothInfiniteSlice K n b f) hc
    (ArchimedeanGL.compactGroupFiniteDifferential K n _ hk)

example : (K : Type u) → [Field K] → [NumberField K] → (n : ℕ) →
    AutomorphicSliceJointFiniteStatement K n :=
  @automorphicSliceJointFinite

end Langlands.Automorphic
