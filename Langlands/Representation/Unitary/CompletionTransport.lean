import Langlands.Representation.Unitary.CompletionIntertwiner

/-! # Covariance and surjectivity of completed isometries -/

noncomputable section
set_option autoImplicit false

namespace Langlands.InvariantPositiveForm

universe uG uV uW

variable {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
  (b : InvariantPositiveForm ρ) (c : InvariantPositiveForm σ)
  (f : ρ.IntertwiningMap σ) (hf : ∀ v w, c.inner (f v) (f w) = b.inner v w)

/-- Any further covariance identity extends when both operators already have
continuous extensions with their prescribed values on the dense carriers. -/
theorem completedIsometry_covariant
    (a : Module.End ℂ V) (d : Module.End ℂ W)
    (A : b.HilbertCompletion →L[ℂ] b.HilbertCompletion)
    (D : c.HilbertCompletion →L[ℂ] c.HilbertCompletion)
    (hA : ∀ v, A (b.toHilbert v) = b.toHilbert (a v))
    (hD : ∀ w, D (c.toHilbert w) = c.toHilbert (d w))
    (hfd : ∀ v, f (a v) = d (f v)) (x : b.HilbertCompletion) :
    b.completedIsometry c f hf (A x) = D (b.completedIsometry c f hf x) := by
  refine b.denseRange_toHilbert.induction_on x ?_ ?_
  · exact isClosed_eq
      ((b.completedIsometry c f hf).continuous.comp A.continuous)
      (D.continuous.comp (b.completedIsometry c f hf).continuous)
  · intro v
    simp only [hA, hD, completedIsometry_toHilbert, hfd]

/-- Surjectivity on the original carrier makes the completed isometry surjective:
its closed image contains the dense embedded target carrier. -/
theorem completedIsometry_surjective (hSurj : Function.Surjective f) :
    Function.Surjective (b.completedIsometry c f hf) := by
  intro y
  refine c.denseRange_toHilbert.induction_on y ?_ ?_
  · exact b.isClosed_range_completedIsometry c f hf
  · intro w
    obtain ⟨v, hv⟩ := hSurj w
    exact ⟨b.toHilbert v,
      (b.completedIsometry_toHilbert c f hf v).trans (congrArg c.toHilbert hv)⟩

/-- Density determines a continuous complex-linear extension uniquely. -/
theorem completedIsometry_unique
    (M : b.HilbertCompletion →L[ℂ] c.HilbertCompletion)
    (hM : ∀ v, M (b.toHilbert v) = c.toHilbert (f v)) :
    M = (b.completedIsometry c f hf).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro x
  refine b.denseRange_toHilbert.induction_on x ?_ ?_
  · exact isClosed_eq M.continuous (b.completedIsometry c f hf).continuous
  · intro v
    exact (hM v).trans (b.completedIsometry_toHilbert c f hf v).symm

/-- An additional covariance equation makes the actual completed range stable
under the target operator. -/
theorem completedRange_covariant
    (a : Module.End ℂ V) (d : Module.End ℂ W)
    (A : b.HilbertCompletion →L[ℂ] b.HilbertCompletion)
    (D : c.HilbertCompletion →L[ℂ] c.HilbertCompletion)
    (hA : ∀ v, A (b.toHilbert v) = b.toHilbert (a v))
    (hD : ∀ w, D (c.toHilbert w) = c.toHilbert (d w))
    (hfd : ∀ v, f (a v) = d (f v))
    {y : c.HilbertCompletion} (hy : y ∈ b.completedRange c f hf) :
    D y ∈ b.completedRange c f hf := by
  obtain ⟨x, hx⟩ := (b.mem_completedRange c f hf y).mp hy
  exact (b.mem_completedRange c f hf (D y)).mpr
    ⟨A x, (b.completedIsometry_covariant c f hf a d A D hA hD hfd x).trans
      (congrArg D hx)⟩

/-- A form-preserving surjective original intertwiner induces a genuine
complex-linear isometric equivalence of the actual Hilbert completions. -/
def completedEquiv (hSurj : Function.Surjective f) :
    b.HilbertCompletion ≃ₗᵢ[ℂ] c.HilbertCompletion :=
  LinearIsometryEquiv.ofSurjective (b.completedIsometry c f hf)
    (b.completedIsometry_surjective c f hf hSurj)

@[simp]
theorem completedEquiv_apply (hSurj : Function.Surjective f) (x : b.HilbertCompletion) :
    b.completedEquiv c f hf hSurj x = b.completedIsometry c f hf x := rfl

@[simp]
theorem completedEquiv_toHilbert (hSurj : Function.Surjective f) (v : V) :
    b.completedEquiv c f hf hSurj (b.toHilbert v) = c.toHilbert (f v) :=
  b.completedIsometry_toHilbert c f hf v

end Langlands.InvariantPositiveForm
