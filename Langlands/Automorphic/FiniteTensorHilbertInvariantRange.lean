import Langlands.Automorphic.FiniteTensorHilbertCovariance

/-! # Invariant completed ranges of actual automorphic tensor slices -/

noncomputable section
open scoped Classical TensorProduct
universe uF uV
set_option autoImplicit false

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.FiniteAdelicGL Langlands.RestrictedTensor

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}
variable {V : FinitePlace F → Type uV}
variable [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]

local instance tensorHilbertInvariantRangeRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance tensorHilbertInvariantRangeContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance tensorHilbertInvariantRangeSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance tensorHilbertInvariantRangeFormsGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance tensorHilbertInvariantRangeFiniteSpaceGroup (S : FiniteRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _
local instance tensorHilbertInvariantRangeLocalSpaceGroup (v : FinitePlace F) (L : LocalRealization F n v) :
    AddCommGroup L.Space := Submodule.addCommGroup _

namespace FiniteTensorPresentation

variable {ρ : ∀ v, Representation ℂ (FiniteLocalGL F n v) (V v)}
variable {E : Finset (FinitePlace F)} {e : ∀ v, V v}
variable {he : ∀ v ∉ E, ∀ g ∈ localIntegral F n v, ρ v g (e v) = e v}
variable {S : FiniteRealization F n} (P : FiniteTensorPresentation F n ρ E e he S)
variable (b : Langlands.InvariantPositiveForm S.representation)

/-- The actual completed slice image, invariant under the original global
completed action at the local inclusion. -/
def sliceHilbertRange (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e) :
    Subrepresentation (b.completedRepresentation.comp (localInclusion F n v).toMonoidHom) :=
  (P.sliceHilbertIntertwiner b v y).range

theorem sliceHilbertRange_toSubmodule (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e) :
    (P.sliceHilbertRange b v y).toSubmodule = P.sliceHilbertSubspace b v y := rfl

theorem coe_sliceHilbertRange (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e) :
    (P.sliceHilbertRange b v y : Set b.HilbertCompletion) =
      Set.range (P.sliceHilbertEmbedding b v y) := rfl

/-- The original global completed operator preserves this image at every
element of the inserted local group. -/
theorem completedOperator_mem_sliceHilbertRange (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e) (g : FiniteLocalGL F n v)
    {x : b.HilbertCompletion} (hx : x ∈ P.sliceHilbertRange b v y) :
    b.completedOperator (localInclusion F n v g) x ∈ P.sliceHilbertRange b v y :=
  (P.sliceHilbertRange b v y).apply_mem_toSubmodule g hx

theorem isClosed_sliceHilbertRange (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e) :
    IsClosed (P.sliceHilbertRange b v y : Set b.HilbertCompletion) :=
  P.isClosed_sliceHilbertSubspace b v y

/-- Invariant packaging retains the closure of the original slice in the same
global completion. -/
theorem coe_sliceHilbertRange_eq_closure (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e) :
    (P.sliceHilbertRange b v y : Set b.HilbertCompletion) =
      closure (Set.range fun f : (P.slice v y).Space =>
        b.toHilbert (P.sliceInclusion v y f)) :=
  P.coe_sliceHilbertSubspace_eq_closure b v y

/-- For a nonzero tail, the completed factor image is this invariant slice. -/
theorem range_factorHilbertEmbedding_eq_sliceHilbertRange (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e)
    (hy : FiniteTensorRealization.TailNonzero F E e v y) :
    Set.range (P.factorHilbertEmbedding b v y hy) =
      (P.sliceHilbertRange b v y : Set b.HilbertCompletion) :=
  P.range_factorHilbertEmbedding b v y hy

/-- The invariant completed slice is the closure of the actual original
pure-tensor images for an explicitly nonzero tail. -/
theorem coe_sliceHilbertRange_eq_closure_pureTensor (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e)
    (hy : FiniteTensorRealization.TailNonzero F E e v y) :
    (P.sliceHilbertRange b v y : Set b.HilbertCompletion) =
      closure (Set.range fun x : V v => b.toHilbert (P.localEquiv v (x ⊗ₜ[ℂ] y))) :=
  (P.range_factorHilbertEmbedding_eq_sliceHilbertRange b v y hy).symm.trans
    (P.range_factorHilbertEmbedding_eq_closure b v y hy)

end FiniteTensorPresentation
end Langlands.Automorphic
