import Langlands.Representation.Unitary.Completion
import Mathlib.Analysis.Normed.Operator.Extend

/-!
# Completed isometric embeddings induced by form-preserving intertwiners
-/

noncomputable section

namespace Langlands.InvariantPositiveForm

universe uG uV uW

variable {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ G V} {σ : Representation ℂ G W}

/-- The pulled-back form is preserved by its defining intertwiner, by definition. -/
theorem inner_map_comap (c : InvariantPositiveForm σ) (f : ρ.IntertwiningMap σ)
    (hf : Function.Injective f) (v w : V) :
    c.inner (f v) (f w) = (c.comap f hf).inner v w := rfl

variable (b : InvariantPositiveForm ρ) (c : InvariantPositiveForm σ)
  (f : ρ.IntertwiningMap σ) (hf : ∀ v w, c.inner (f v) (f w) = b.inner v w)

/-- The actual intertwiner, transported to the form-dependent normed carriers.
The form-preservation identity makes it a complex-linear isometry. -/
def normedIntertwiner : b.NormedCarrier →ₗᵢ[ℂ] c.NormedCarrier :=
  (c.toNormedCarrier.toLinearMap.comp
    (f.toLinearMap.comp b.toNormedCarrier.symm.toLinearMap)).isometryOfInner hf

@[simp]
theorem normedIntertwiner_toNormedCarrier (v : V) :
    b.normedIntertwiner c f hf (b.toNormedCarrier v) = c.toNormedCarrier (f v) := rfl

include hf in
/-- Form preservation and definiteness of `b` force the original intertwiner to be injective. -/
theorem injective_of_inner_map : Function.Injective f := by
  intro v w h
  apply b.toNormedCarrier.injective
  apply (b.normedIntertwiner c f hf).injective
  rw [normedIntertwiner_toNormedCarrier, normedIntertwiner_toNormedCarrier, h]

/-- Extension of the normed intertwiner to the actual Hilbert completions. -/
def completedIsometry : b.HilbertCompletion →ₗᵢ[ℂ] c.HilbertCompletion :=
  (b.normedIntertwiner c f hf).completion

@[simp]
theorem completedIsometry_toHilbert (v : V) :
    b.completedIsometry c f hf (b.toHilbert v) = c.toHilbert (f v) :=
  LinearIsometry.completion_apply_coe _ _

theorem completedIsometry_completedOperator (g : G) (x : b.HilbertCompletion) :
    b.completedIsometry c f hf (b.completedOperator g x) =
      c.completedOperator g (b.completedIsometry c f hf x) := by
  refine b.denseRange_toHilbert.induction_on x ?_ ?_
  · exact isClosed_eq
      ((b.completedIsometry c f hf).continuous.comp (b.completedOperator g).continuous)
      ((c.completedOperator g).continuous.comp (b.completedIsometry c f hf).continuous)
  · intro v
    simp [f.isIntertwining]

theorem completedIsometry_completedRepresentation (g : G) (x : b.HilbertCompletion) :
    b.completedIsometry c f hf (b.completedRepresentation g x) =
      c.completedRepresentation g (b.completedIsometry c f hf x) :=
  b.completedIsometry_completedOperator c f hf g x

theorem completedIsometry_injective : Function.Injective (b.completedIsometry c f hf) :=
  (b.completedIsometry c f hf).injective

@[simp]
theorem norm_completedIsometry (x : b.HilbertCompletion) :
    ‖b.completedIsometry c f hf x‖ = ‖x‖ :=
  (b.completedIsometry c f hf).norm_map x

@[simp]
theorem inner_completedIsometry (x y : b.HilbertCompletion) :
    inner ℂ (b.completedIsometry c f hf x) (b.completedIsometry c f hf y) = inner ℂ x y :=
  (b.completedIsometry c f hf).inner_map_map x y

/-- Completeness of the source completion makes the isometric image closed. -/
theorem isClosed_range_completedIsometry :
    IsClosed (Set.range (b.completedIsometry c f hf)) :=
  (b.completedIsometry c f hf).isometry.isClosedEmbedding.isClosed_range

/-- The completed isometry as an actual continuous complex-linear map. -/
def completedContinuousLinearMap : b.HilbertCompletion →L[ℂ] c.HilbertCompletion :=
  (b.completedIsometry c f hf).toContinuousLinearMap

@[simp]
theorem completedContinuousLinearMap_apply (x : b.HilbertCompletion) :
    b.completedContinuousLinearMap c f hf x = b.completedIsometry c f hf x := rfl

theorem isClosed_range_completedContinuousLinearMap :
    IsClosed (Set.range (b.completedContinuousLinearMap c f hf)) :=
  b.isClosed_range_completedIsometry c f hf

/-- The completed isometry as an intertwiner of the completed representations. -/
def completedIntertwiner :
    b.completedRepresentation.IntertwiningMap c.completedRepresentation where
  toLinearMap := (b.completedIsometry c f hf).toLinearMap
  isIntertwining' g := LinearMap.ext (b.completedIsometry_completedRepresentation c f hf g)

@[simp]
theorem completedIntertwiner_apply (x : b.HilbertCompletion) :
    b.completedIntertwiner c f hf x = b.completedIsometry c f hf x := rfl

theorem continuous_completedIntertwiner : Continuous (b.completedIntertwiner c f hf) :=
  (b.completedIsometry c f hf).continuous

/-- The image of the completed isometry, as an invariant complex subspace of the
target completion. -/
def completedRange : Subrepresentation c.completedRepresentation :=
  (b.completedIntertwiner c f hf).range

theorem completedRange_toSubmodule :
    (b.completedRange c f hf).toSubmodule =
      LinearMap.range (b.completedIsometry c f hf).toLinearMap := rfl

theorem mem_completedRange (y : c.HilbertCompletion) :
    y ∈ b.completedRange c f hf ↔ ∃ x, b.completedIsometry c f hf x = y := Iff.rfl

theorem coe_completedRange :
    (b.completedRange c f hf : Set c.HilbertCompletion) =
      Set.range (b.completedIsometry c f hf) := rfl

theorem isClosed_completedRange :
    IsClosed (b.completedRange c f hf : Set c.HilbertCompletion) := by
  rw [coe_completedRange]
  exact b.isClosed_range_completedIsometry c f hf

/-- The completed range is the closure of the image of the original algebraic carrier. -/
theorem coe_completedRange_eq_closure :
    (b.completedRange c f hf : Set c.HilbertCompletion) =
      closure (Set.range fun v : V => c.toHilbert (f v)) := by
  rw [coe_completedRange]
  apply subset_antisymm
  · rintro _ ⟨x, rfl⟩
    refine b.denseRange_toHilbert.induction_on x ?_ ?_
    · exact isClosed_closure.preimage (b.completedIsometry c f hf).continuous
    · intro v
      exact subset_closure ⟨v, (b.completedIsometry_toHilbert c f hf v).symm⟩
  · refine closure_minimal ?_ (b.isClosed_range_completedIsometry c f hf)
    rintro _ ⟨v, rfl⟩
    exact ⟨b.toHilbert v, b.completedIsometry_toHilbert c f hf v⟩

end Langlands.InvariantPositiveForm
