import Langlands.Automorphic.FiniteTensorHilbertInvariantRange
import Langlands.Representation.Classification.JuxtaposedJacquetImage

/-! # Representation equivalences onto actual invariant tensor slices -/

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

local instance tensorHilbertRepresentationEquivRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance tensorHilbertRepresentationEquivContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance tensorHilbertRepresentationEquivSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance tensorHilbertRepresentationEquivFormsGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance tensorHilbertRepresentationEquivFiniteSpaceGroup (S : FiniteRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _
local instance tensorHilbertRepresentationEquivLocalSpaceGroup (v : FinitePlace F) (L : LocalRealization F n v) :
    AddCommGroup L.Space := Submodule.addCommGroup _

namespace FiniteTensorPresentation

variable {ρ : ∀ v, Representation ℂ (FiniteLocalGL F n v) (V v)}
variable {E : Finset (FinitePlace F)} {e : ∀ v, V v}
variable {he : ∀ v ∉ E, ∀ g ∈ localIntegral F n v, ρ v g (e v) = e v}
variable {S : FiniteRealization F n} (P : FiniteTensorPresentation F n ρ E e he S)
variable (b : Langlands.InvariantPositiveForm S.representation)

/-- The completed slice representation is equivalent to its actual invariant
image for the restriction of the original global completed action. -/
def sliceHilbertRepresentationEquiv (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e) :=
  Langlands.Classification.JuxtaposedShuffle.rangeEquivOfInjective
    (P.sliceHilbertIntertwiner b v y) (P.sliceHilbertEmbedding b v y).injective

/-- The existing factor-to-slice Hilbert equivalence as an equivalence of the
two actual completed local representations. -/
def factorSliceHilbertRepresentationEquiv (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e)
    (hy : FiniteTensorRealization.TailNonzero F E e v y) :=
  Representation.Equiv.mk
    (ρ := (P.factorUnitaryForm b v y hy).completedRepresentation)
    (σ := (P.sliceUnitaryForm b v y).completedRepresentation)
    (P.factorSliceHilbertEquiv b v y hy).toLinearEquiv
    (fun g => LinearMap.ext (P.factorSliceHilbertEquiv_completedOperator b v y hy g))

/-- The specified factor completion carries exactly the representation on its
whole fixed-tail invariant slice of the original global completion. -/
def factorHilbertRepresentationEquiv (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e)
    (hy : FiniteTensorRealization.TailNonzero F E e v y) :=
  (P.factorSliceHilbertRepresentationEquiv b v y hy).trans
    (P.sliceHilbertRepresentationEquiv b v y)

end FiniteTensorPresentation
end Langlands.Automorphic
