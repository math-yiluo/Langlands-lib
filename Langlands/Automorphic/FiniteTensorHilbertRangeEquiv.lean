import Langlands.Automorphic.FiniteTensorHilbertInvariantRange

/-! # Hilbert equivalences onto actual invariant tensor slices -/

noncomputable section
open scoped Classical TensorProduct
universe uF uV
set_option autoImplicit false
set_option maxHeartbeats 20000

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.FiniteAdelicGL Langlands.RestrictedTensor

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}
variable {V : FinitePlace F → Type uV}
variable [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]

local instance tensorHilbertRangeEquivRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance tensorHilbertRangeEquivContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance tensorHilbertRangeEquivSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance tensorHilbertRangeEquivFormsGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance tensorHilbertRangeEquivFiniteSpaceGroup (S : FiniteRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _
local instance tensorHilbertRangeEquivLocalSpaceGroup (v : FinitePlace F) (L : LocalRealization F n v) :
    AddCommGroup L.Space := Submodule.addCommGroup _

namespace FiniteTensorPresentation

variable {ρ : ∀ v, Representation ℂ (FiniteLocalGL F n v) (V v)}
variable {E : Finset (FinitePlace F)} {e : ∀ v, V v}
variable {he : ∀ v ∉ E, ∀ g ∈ localIntegral F n v, ρ v g (e v) = e v}
variable {S : FiniteRealization F n} (P : FiniteTensorPresentation F n ρ E e he S)
variable (b : Langlands.InvariantPositiveForm S.representation)

/-- The actual invariant completed slice is complete for its inherited metric. -/
instance completeSpace_sliceHilbertRange (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e) :
    CompleteSpace (P.sliceHilbertRange b v y).toSubmodule :=
  (P.isClosed_sliceHilbertRange b v y).isComplete.completeSpace_coe

/-- The slice completion is isometrically equivalent to its actual invariant
image in the original global completion, including zero slices. -/
def sliceHilbertRangeEquiv (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e) :=
  (P.sliceHilbertEmbedding b v y).equivRange

/-- A nonzero complementary tensor identifies the specified factor completion
with the closed invariant slice carrying its inherited inner product. -/
def factorHilbertRangeEquiv (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e)
    (hy : FiniteTensorRealization.TailNonzero F E e v y) :=
  (P.factorSliceHilbertEquiv b v y hy).trans (P.sliceHilbertRangeEquiv b v y)

end FiniteTensorPresentation
end Langlands.Automorphic
