import Langlands.Automorphic.FiniteTensorHilbertComponent

/-! # Smooth submodule of an actual completed tensor slice -/

noncomputable section
open scoped Classical TensorProduct
universe uF uV
set_option autoImplicit false
set_option maxHeartbeats 20000

namespace Langlands.TensorSmoothRangeAux

universe uG uA uB

variable {G : Type uG} [Monoid G]
variable {A : Type uA} [AddCommGroup A] [Module ℂ A]
variable {B : Type uB} [AddCommGroup B] [Module ℂ B]
variable {σ : Representation ℂ G A} {τ : Representation ℂ G B}

/-- Restrict an intertwiner to a specified subrepresentation equal to its image. -/
def rangeRestriction (f : σ.IntertwiningMap τ) (R : Subrepresentation τ)
    (hR : f.range.toSubmodule = R.toSubmodule) :
    σ.IntertwiningMap R.toRepresentation where
  toLinearMap := f.toLinearMap.codRestrict R.toSubmodule (by
    intro x
    rw [← hR]
    exact ⟨x, rfl⟩)
  isIntertwining' g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact Representation.IntertwiningMap.isIntertwining _ _ f g x

theorem rangeRestriction_apply_val (f : σ.IntertwiningMap τ) (R : Subrepresentation τ)
    (hR : f.range.toSubmodule = R.toSubmodule) (x : A) :
    (rangeRestriction f R hR x).val = f x := rfl

theorem rangeRestriction_surjective (f : σ.IntertwiningMap τ) (R : Subrepresentation τ)
    (hR : f.range.toSubmodule = R.toSubmodule) :
    Function.Surjective (rangeRestriction f R hR) := by
  intro z
  have hz : z.val ∈ f.range.toSubmodule := hR.symm ▸ z.property
  obtain ⟨x, hx⟩ := hz
  exact ⟨x, Subtype.ext hx⟩

end Langlands.TensorSmoothRangeAux

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.FiniteAdelicGL Langlands.RestrictedTensor

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}
variable {V : FinitePlace F → Type uV}
variable [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]

local instance tensorHilbertSmoothRangeRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance tensorHilbertSmoothRangeContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance tensorHilbertSmoothRangeSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance tensorHilbertSmoothRangeFormsGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance tensorHilbertSmoothRangeFiniteSpaceGroup (S : FiniteRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _
local instance tensorHilbertSmoothRangeLocalSpaceGroup (v : FinitePlace F) (L : LocalRealization F n v) :
    AddCommGroup L.Space := Submodule.addCommGroup _

namespace FiniteTensorPresentation

variable {ρ : ∀ v, Representation ℂ (FiniteLocalGL F n v) (V v)}
variable {E : Finset (FinitePlace F)} {e : ∀ v, V v}
variable {he : ∀ v ∉ E, ∀ g ∈ localIntegral F n v, ρ v g (e v) = e v}
variable {S : FiniteRealization F n} (P : FiniteTensorPresentation F n ρ E e he S)
variable (b : Langlands.InvariantPositiveForm S.representation)

/-- The intrinsic locally smooth part of the completed tensor slice, with the
inherited action of the inserted local group. -/
def sliceHilbertSmoothRange (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e) :
    Subrepresentation (b.completedRepresentation.comp (localInclusion F n v).toMonoidHom) :=
  P.sliceHilbertRange b v y ⊓
    Langlands.smoothSubrepresentation (b.completedRepresentation.comp (localInclusion F n v).toMonoidHom)

/-- An equality of actual ambient submodules records smooth-vector recovery. -/
theorem factorHilbertAlgebraicIntertwiner_range (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e)
    (hy : FiniteTensorRealization.TailNonzero F E e v y)
    (hρ : IsAdmissible (ρ v)) :
    (P.factorHilbertAlgebraicIntertwiner b v y hy).range.toSubmodule =
      (P.sliceHilbertRange b v y).toSubmodule ⊓
        smoothVectors (b.completedRepresentation.comp (localInclusion F n v).toMonoidHom) := by
  apply Submodule.ext
  intro z
  exact (P.mem_sliceHilbertRange_and_smooth_iff b v y hy hρ z).symm

/-- The original factor maps into the intrinsic smooth slice. -/
def factorHilbertSmoothIntertwiner (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e)
    (hy : FiniteTensorRealization.TailNonzero F E e v y)
    (hρ : IsAdmissible (ρ v)) :
    (ρ v).IntertwiningMap (P.sliceHilbertSmoothRange b v y).toRepresentation :=
  TensorSmoothRangeAux.rangeRestriction
    (P.factorHilbertAlgebraicIntertwiner b v y hy) (P.sliceHilbertSmoothRange b v y)
    (P.factorHilbertAlgebraicIntertwiner_range b v y hy hρ)


end FiniteTensorPresentation
end Langlands.Automorphic
