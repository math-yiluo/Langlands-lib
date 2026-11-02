import Langlands.Automorphic.FiniteTensorUnitaryForm
import Langlands.Representation.Unitary.CompletionTransport

/-! # Hilbert embeddings of actual automorphic tensor slices -/

noncomputable section
open scoped Classical TensorProduct
universe uF uV
set_option autoImplicit false

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.FiniteAdelicGL Langlands.RestrictedTensor

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}
variable {V : FinitePlace F → Type uV}
variable [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]

local instance tensorHilbertRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance tensorHilbertContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance tensorHilbertSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance tensorHilbertFormsGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance tensorHilbertFiniteSpaceGroup (S : FiniteRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _
local instance tensorHilbertLocalSpaceGroup (v : FinitePlace F) (L : LocalRealization F n v) :
    AddCommGroup L.Space := Submodule.addCommGroup _

namespace FiniteTensorPresentation

variable {ρ : ∀ v, Representation ℂ (FiniteLocalGL F n v) (V v)}
variable {E : Finset (FinitePlace F)} {e : ∀ v, V v}
variable {he : ∀ v ∉ E, ∀ g ∈ localIntegral F n v, ρ v g (e v) = e v}
variable {S : FiniteRealization F n} (P : FiniteTensorPresentation F n ρ E e he S)
variable (b : Langlands.InvariantPositiveForm S.representation)

/-- The genuine separated local tensor carrier completes to the whole chosen
completion, with the local action restricted along the actual local insertion. -/
def separatedHilbertEquiv (v : FinitePlace F) :=
  (P.separatedUnitaryForm b v).completedEquiv
    (b.comp (localInclusion F n v).toMonoidHom)
    (P.localEquiv v).toIntertwiningMap (fun _ _ => rfl) (P.localEquiv v).surjective

/-- Complete the actual slice inclusion isometrically into the same global
positive-form completion. This also permits the zero slice. -/
def sliceHilbertEmbedding (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e) :=
  (P.sliceUnitaryForm b v y).completedIsometry
    (b.comp (localInclusion F n v).toMonoidHom)
    (P.sliceInclusion v y) (fun _ _ => rfl)

/-- The actual factor-to-slice equivalence extends to the forms already extracted
from the same global form. The nonzero complementary tensor remains explicit. -/
def factorSliceHilbertEquiv (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e)
    (hy : FiniteTensorRealization.TailNonzero F E e v y) :=
  (P.factorUnitaryForm b v y hy).completedEquiv (P.sliceUnitaryForm b v y)
    (P.sliceEquiv v y hy).toIntertwiningMap (fun _ _ => rfl)
      (P.sliceEquiv v y hy).surjective

/-- A specified local factor embeds isometrically in the global completion
through its actual fixed-tail slice. -/
def factorHilbertEmbedding (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e)
    (hy : FiniteTensorRealization.TailNonzero F E e v y) :=
  (P.sliceHilbertEmbedding b v y).comp
    (P.factorSliceHilbertEquiv b v y hy).toLinearIsometry

@[simp]
theorem separatedHilbertEquiv_toHilbert (v : FinitePlace F)
    (z : V v ⊗[ℂ] LocalTensorTail (K := ℂ) F E v e) :
    P.separatedHilbertEquiv b v ((P.separatedUnitaryForm b v).toHilbert z) =
      b.toHilbert (P.localEquiv v z) :=
  (P.separatedUnitaryForm b v).completedEquiv_toHilbert
    (b.comp (localInclusion F n v).toMonoidHom)
    (P.localEquiv v).toIntertwiningMap (fun _ _ => rfl) (P.localEquiv v).surjective z

@[simp]
theorem sliceHilbertEmbedding_toHilbert (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e) (f : (P.slice v y).Space) :
    P.sliceHilbertEmbedding b v y ((P.sliceUnitaryForm b v y).toHilbert f) =
      b.toHilbert (P.sliceInclusion v y f) :=
  (P.sliceUnitaryForm b v y).completedIsometry_toHilbert
    (b.comp (localInclusion F n v).toMonoidHom)
    (P.sliceInclusion v y) (fun _ _ => rfl) f

@[simp]
theorem factorSliceHilbertEquiv_toHilbert (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e)
    (hy : FiniteTensorRealization.TailNonzero F E e v y) (x : V v) :
    P.factorSliceHilbertEquiv b v y hy ((P.factorUnitaryForm b v y hy).toHilbert x) =
      (P.sliceUnitaryForm b v y).toHilbert (P.sliceEquiv v y hy x) :=
  (P.factorUnitaryForm b v y hy).completedEquiv_toHilbert (P.sliceUnitaryForm b v y)
    (P.sliceEquiv v y hy).toIntertwiningMap (fun _ _ => rfl)
      (P.sliceEquiv v y hy).surjective x

@[simp]
theorem factorHilbertEmbedding_toHilbert (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e)
    (hy : FiniteTensorRealization.TailNonzero F E e v y) (x : V v) :
    P.factorHilbertEmbedding b v y hy ((P.factorUnitaryForm b v y hy).toHilbert x) =
      b.toHilbert (P.localEquiv v (x ⊗ₜ[ℂ] y)) := by
  change P.sliceHilbertEmbedding b v y
    (P.factorSliceHilbertEquiv b v y hy ((P.factorUnitaryForm b v y hy).toHilbert x)) = _
  exact (congrArg (P.sliceHilbertEmbedding b v y)
    (P.factorSliceHilbertEquiv_toHilbert b v y hy x)).trans
      ((P.sliceHilbertEmbedding_toHilbert b v y (P.sliceEquiv v y hy x)).trans
        (congrArg b.toHilbert (P.sliceInclusion_sliceEquiv v y hy x)))

end FiniteTensorPresentation
end Langlands.Automorphic
