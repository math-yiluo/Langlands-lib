import Langlands.Automorphic.FiniteTensorHilbertEmbedding

/-! # Closed Hilbert subspaces of actual automorphic tensor slices -/

noncomputable section
open scoped Classical TensorProduct
universe uF uV
set_option autoImplicit false

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.FiniteAdelicGL Langlands.RestrictedTensor

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}
variable {V : FinitePlace F → Type uV}
variable [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]

local instance tensorHilbertRangeRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance tensorHilbertRangeContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance tensorHilbertRangeSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance tensorHilbertRangeFormsGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance tensorHilbertRangeFiniteSpaceGroup (S : FiniteRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _
local instance tensorHilbertRangeLocalSpaceGroup (v : FinitePlace F) (L : LocalRealization F n v) :
    AddCommGroup L.Space := Submodule.addCommGroup _

namespace FiniteTensorPresentation

variable {ρ : ∀ v, Representation ℂ (FiniteLocalGL F n v) (V v)}
variable {E : Finset (FinitePlace F)} {e : ∀ v, V v}
variable {he : ∀ v ∉ E, ∀ g ∈ localIntegral F n v, ρ v g (e v) = e v}
variable {S : FiniteRealization F n} (P : FiniteTensorPresentation F n ρ E e he S)
variable (b : Langlands.InvariantPositiveForm S.representation)

/-- The actual completed fixed-tail slice as a complex submodule of the chosen
same global completion. No nonzero-tail hypothesis is required. -/
def sliceHilbertSubspace (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e) : Submodule ℂ b.HilbertCompletion :=
  (P.sliceHilbertEmbedding b v y).toLinearMap.range

theorem coe_sliceHilbertSubspace (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e) :
    (P.sliceHilbertSubspace b v y : Set b.HilbertCompletion) =
      Set.range (P.sliceHilbertEmbedding b v y) := rfl

/-- Completeness makes the actual slice image closed. -/
theorem isClosed_sliceHilbertSubspace (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e) :
    IsClosed (P.sliceHilbertSubspace b v y : Set b.HilbertCompletion) :=
  (P.sliceHilbertEmbedding b v y).isometry.isClosedEmbedding.isClosed_range

/-- The completed slice is exactly the closure of the embedded original slice. -/
theorem coe_sliceHilbertSubspace_eq_closure (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e) :
    (P.sliceHilbertSubspace b v y : Set b.HilbertCompletion) =
      closure (Set.range fun f : (P.slice v y).Space =>
        b.toHilbert (P.sliceInclusion v y f)) :=
  (P.sliceUnitaryForm b v y).coe_completedRange_eq_closure
    (b.comp (localInclusion F n v).toMonoidHom)
    (P.sliceInclusion v y) (fun _ _ => rfl)

/-- For a specified nonzero tail, the factor image is the whole completed slice. -/
theorem range_factorHilbertEmbedding (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e)
    (hy : FiniteTensorRealization.TailNonzero F E e v y) :
    Set.range (P.factorHilbertEmbedding b v y hy) =
      (P.sliceHilbertSubspace b v y : Set b.HilbertCompletion) :=
  (P.factorSliceHilbertEquiv b v y hy).surjective.range_comp (P.sliceHilbertEmbedding b v y)

/-- The factor image is exactly the closed pure-tensor slice for the chosen tail. -/
theorem range_factorHilbertEmbedding_eq_closure (v : FinitePlace F)
    (y : LocalTensorTail (K := ℂ) F E v e)
    (hy : FiniteTensorRealization.TailNonzero F E e v y) :
    Set.range (P.factorHilbertEmbedding b v y hy) =
      closure (Set.range fun x : V v => b.toHilbert (P.localEquiv v (x ⊗ₜ[ℂ] y))) := by
  apply subset_antisymm
  · rintro _ ⟨x, rfl⟩
    refine (P.factorUnitaryForm b v y hy).denseRange_toHilbert.induction_on x ?_ ?_
    · exact isClosed_closure.preimage (P.factorHilbertEmbedding b v y hy).continuous
    · intro z
      exact subset_closure ⟨z, (P.factorHilbertEmbedding_toHilbert b v y hy z).symm⟩
  · refine closure_minimal ?_
      (P.factorHilbertEmbedding b v y hy).isometry.isClosedEmbedding.isClosed_range
    rintro _ ⟨z, rfl⟩
    exact ⟨(P.factorUnitaryForm b v y hy).toHilbert z,
      P.factorHilbertEmbedding_toHilbert b v y hy z⟩

end FiniteTensorPresentation
end Langlands.Automorphic
