import Langlands.Representation.Unitary.CompletionOperations

/-! # Completed intertwiners into a restricted representation -/

noncomputable section
set_option autoImplicit false

namespace Langlands.InvariantPositiveForm

universe uG uH uV uW

section Equivalence

variable {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
  (b : InvariantPositiveForm ρ) (c : InvariantPositiveForm σ)
  (f : ρ.IntertwiningMap σ) (hf : ∀ v w, c.inner (f v) (f w) = b.inner v w)

/-- The completed equivalence intertwines the original completed operators. -/
theorem completedEquiv_completedOperator (hSurj : Function.Surjective f)
    (g : G) (x : b.HilbertCompletion) :
    b.completedEquiv c f hf hSurj (b.completedOperator g x) =
      c.completedOperator g (b.completedEquiv c f hf hSurj x) :=
  b.completedIsometry_completedOperator c f hf g x

end Equivalence

section RestrictedTarget

variable {G : Type uG} [Group G] {H : Type uH} [Group H]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {ρ : Representation ℂ H V} {σ : Representation ℂ G W}
  (b : InvariantPositiveForm ρ) (c : InvariantPositiveForm σ) (φ : H →* G)
  (f : ρ.IntertwiningMap (σ.comp φ))
  (hf : ∀ v w, c.inner (f v) (f w) = b.inner v w)

/-- Restricting the target form keeps its completion and gives covariance
under the actual image of the group homomorphism. -/
theorem completedIsometry_comp_completedOperator (h : H) (x : b.HilbertCompletion) :
    b.completedIsometry (c.comp φ) f hf (b.completedOperator h x) =
      c.completedOperator (φ h) (b.completedIsometry (c.comp φ) f hf x) :=
  (b.completedIsometry_completedOperator (c.comp φ) f hf h x).trans
    (c.comp_completedOperator φ h (b.completedIsometry (c.comp φ) f hf x))

/-- The surjective case has the same actual-image covariance. -/
theorem completedEquiv_comp_completedOperator (hSurj : Function.Surjective f)
    (h : H) (x : b.HilbertCompletion) :
    b.completedEquiv (c.comp φ) f hf hSurj (b.completedOperator h x) =
      c.completedOperator (φ h) (b.completedEquiv (c.comp φ) f hf hSurj x) :=
  b.completedIsometry_comp_completedOperator c φ f hf h x

/-- The genuine completed map into the restriction of the original completed
target representation, on its unchanged Hilbert carrier. -/
def completedIntertwinerAlong :
    b.completedRepresentation.IntertwiningMap (c.completedRepresentation.comp φ) where
  toLinearMap := (b.completedIsometry (c.comp φ) f hf).toLinearMap
  isIntertwining' h :=
    LinearMap.ext (b.completedIsometry_comp_completedOperator c φ f hf h)

@[simp]
theorem completedIntertwinerAlong_apply (x : b.HilbertCompletion) :
    b.completedIntertwinerAlong c φ f hf x =
      b.completedIsometry (c.comp φ) f hf x := rfl

theorem continuous_completedIntertwinerAlong :
    Continuous (b.completedIntertwinerAlong c φ f hf) :=
  (b.completedIsometry (c.comp φ) f hf).continuous

/-- The actual closed image, invariant under the original target action at the
homomorphism images. -/
def completedRangeAlong : Subrepresentation (c.completedRepresentation.comp φ) :=
  (b.completedIntertwinerAlong c φ f hf).range

theorem completedRangeAlong_toSubmodule :
    (b.completedRangeAlong c φ f hf).toSubmodule =
      (b.completedIsometry (c.comp φ) f hf).toLinearMap.range := rfl

theorem coe_completedRangeAlong :
    (b.completedRangeAlong c φ f hf : Set c.HilbertCompletion) =
      Set.range (b.completedIsometry (c.comp φ) f hf) := rfl

theorem isClosed_completedRangeAlong :
    IsClosed (b.completedRangeAlong c φ f hf : Set c.HilbertCompletion) :=
  b.isClosed_range_completedIsometry (c.comp φ) f hf

/-- The invariant completed image is exactly the closure of the original
embedded image in the same target completion. -/
theorem coe_completedRangeAlong_eq_closure :
    (b.completedRangeAlong c φ f hf : Set c.HilbertCompletion) =
      closure (Set.range fun v : V => c.toHilbert (f v)) :=
  b.coe_completedRange_eq_closure (c.comp φ) f hf

end RestrictedTarget
end Langlands.InvariantPositiveForm
