import Langlands.Automorphic.FiniteTensorHilbertSmoothRange

/-! # Original-factor equivalences onto intrinsic smooth tensor slices -/

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

/-- An injective original map stays injective after restricting its codomain. -/
theorem rangeRestriction_injective (f : σ.IntertwiningMap τ) (R : Subrepresentation τ)
    (hR : f.range.toSubmodule = R.toSubmodule) (hf : Function.Injective f) :
    Function.Injective (rangeRestriction f R hR) := by
  intro x y hxy
  exact hf (congrArg Subtype.val hxy)

/-- Identify an injective intertwiner's source with a specified actual image. -/
def rangeRestrictionEquiv (f : σ.IntertwiningMap τ) (R : Subrepresentation τ)
    (hR : f.range.toSubmodule = R.toSubmodule) (hf : Function.Injective f) :
    σ.Equiv R.toRepresentation :=
  (rangeRestriction f R hR).ofBijective
    ⟨rangeRestriction_injective f R hR hf, rangeRestriction_surjective f R hR⟩

/-- The equivalence has exactly the original ambient forward value. -/
theorem rangeRestrictionEquiv_apply_val (f : σ.IntertwiningMap τ)
    (R : Subrepresentation τ) (hR : f.range.toSubmodule = R.toSubmodule)
    (hf : Function.Injective f) (x : A) :
    (rangeRestrictionEquiv f R hR hf x).val = f x := rfl

/-- The inverse recovers an actual preimage under the same ambient map. -/
theorem rangeRestrictionEquiv_symm_apply (f : σ.IntertwiningMap τ)
    (R : Subrepresentation τ) (hR : f.range.toSubmodule = R.toSubmodule)
    (hf : Function.Injective f) (z : R.toSubmodule) :
    f ((rangeRestrictionEquiv f R hR hf).symm z) = z.val :=
  congrArg Subtype.val ((rangeRestrictionEquiv f R hR hf).apply_symm_apply z)

end Langlands.TensorSmoothRangeAux

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.FiniteAdelicGL Langlands.RestrictedTensor

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}
variable {V : FinitePlace F → Type uV}
variable [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]

local instance tensorHilbertSmoothEquivRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance tensorHilbertSmoothEquivContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance tensorHilbertSmoothEquivSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance tensorHilbertSmoothEquivFormsGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance tensorHilbertSmoothEquivFiniteSpaceGroup (S : FiniteRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _
local instance tensorHilbertSmoothEquivLocalSpaceGroup (v : FinitePlace F) (L : LocalRealization F n v) :
    AddCommGroup L.Space := Submodule.addCommGroup _

namespace FiniteTensorPresentation

variable {ρ : ∀ v, Representation ℂ (FiniteLocalGL F n v) (V v)}
variable {E : Finset (FinitePlace F)} {e : ∀ v, V v}
variable {he : ∀ v ∉ E, ∀ g ∈ localIntegral F n v, ρ v g (e v) = e v}
variable {S : FiniteRealization F n} (P : FiniteTensorPresentation F n ρ E e he S)
variable (b : Langlands.InvariantPositiveForm S.representation)

/-- The actual original-factor map is injective, before any admissibility input. -/
theorem factorHilbertAlgebraicIntertwiner_injective (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e)
    (hy : FiniteTensorRealization.TailNonzero F E e v y) :
    Function.Injective (P.factorHilbertAlgebraicIntertwiner b v y hy) :=
  (P.factorHilbertEmbedding b v y hy).injective.comp
    (P.factorUnitaryForm b v y hy).toHilbert_injective

/-- The given original admissible factor is equivalent to the intrinsic smooth
subrepresentation of its actual completed tensor slice. -/
def factorHilbertSmoothEquiv (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e)
    (hy : FiniteTensorRealization.TailNonzero F E e v y)
    (hρ : IsAdmissible (ρ v)) :=
  TensorSmoothRangeAux.rangeRestrictionEquiv
    (P.factorHilbertAlgebraicIntertwiner b v y hy) (P.sliceHilbertSmoothRange b v y)
    (P.factorHilbertAlgebraicIntertwiner_range b v y hy hρ)
    (P.factorHilbertAlgebraicIntertwiner_injective b v y hy)

end FiniteTensorPresentation
end Langlands.Automorphic
