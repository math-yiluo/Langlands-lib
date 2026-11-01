import Langlands.Automorphic.PreservationStatement
import Langlands.Automorphic.SliceFinitenessProof
import Langlands.Global.ArchimedeanFiniteDifferentialGrowth

/-! # Polynomial growth of genuine automorphic enveloping derivatives -/

noncomputable section
universe u
set_option autoImplicit false

namespace Langlands.Automorphic

open Langlands.Global

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- The genuine enveloping differential of every actual automorphic form
has polynomial growth on every finite adelic slice. -/
theorem automorphicDifferentialGrowth :
    AutomorphicDifferentialGrowthStatement K n := by
  intro a f b
  have hf := (mem_automorphicSubrepresentation K n f.val).mp f.property
  have hz : ArchimedeanGL.IsCenterFinite K n
      (smoothInfiniteSlice K n b (finiteSmoothInclusion K n f.val)) :=
    (SliceFinitenessProof.sliceFiniteness K n).1
      (smoothSliceFamily K n (finiteSmoothInclusion K n f.val)) hf.2.2.1 b
  have hk := (SliceFinitenessProof.sliceFiniteness K n).2
    (standardInfiniteCompact K n) (finiteSmoothInclusion K n f.val) hf.2.1 b
  have hg := ArchimedeanGL.enveloping_hasPolynomialGrowth_of_finite
    (smoothInfiniteSlice K n b (finiteSmoothInclusion K n f.val))
    hk hz (hf.2.2.2 b) a
  change ArchimedeanGL.HasPolynomialGrowth K n
    (finiteSmoothSlice K n b (finiteSmoothEnvelopingAction K n a f.val)).val
  rw [finiteSmoothSlice_envelopingAction]
  exact hg

example : ∀ (K : Type u) [Field K] [NumberField K] (n : ℕ),
    AutomorphicDifferentialGrowthStatement K n :=
  @automorphicDifferentialGrowth

end Langlands.Automorphic
