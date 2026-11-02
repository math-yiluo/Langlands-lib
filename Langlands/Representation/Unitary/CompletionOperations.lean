import Langlands.Representation.Unitary.CompletionTransport
import Langlands.Representation.Unitary.Restriction
import Langlands.Representation.Unitary.Twist

/-! # Completed restriction, scalar twist and inverse-transported forms -/

noncomputable section
set_option autoImplicit false

namespace Langlands.InvariantPositiveForm

universe uG uH uV uW

variable {G : Type uG} [Group G] {H : Type uH} [Group H]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ G V} (b : InvariantPositiveForm ρ)

/-- Restriction uses the same positive core, completion and canonical embedding. -/
theorem comp_toHilbert (φ : H →* G) (v : V) :
    (b.comp φ).toHilbert v = b.toHilbert v := rfl

/-- The completed restricted operator is the original completed operator at the image. -/
theorem comp_completedOperator (φ : H →* G) (h : H) (x : b.HilbertCompletion) :
    (b.comp φ).completedOperator h x = b.completedOperator (φ h) x := by
  refine b.denseRange_toHilbert.induction_on x ?_ ?_
  · exact isClosed_eq ((b.comp φ).completedOperator h).continuous
      (b.completedOperator (φ h)).continuous
  · intro v
    exact ((b.comp φ).completedOperator_toHilbert h v).trans
      (b.completedOperator_toHilbert (φ h) v).symm

/-- Completion of a restricted representation agrees with restriction after completion. -/
theorem comp_completedRepresentation (φ : H →* G) :
    (b.comp φ).completedRepresentation = b.completedRepresentation.comp φ := by
  ext h x
  exact b.comp_completedOperator φ h x

/-- Unit-modulus twisting uses the unchanged canonical embedding. -/
theorem twist_toHilbert (χ : G →* ℂˣ) (hχ : ∀ g, ‖(χ g : ℂ)‖ = 1) (v : V) :
    (b.twist χ hχ).toHilbert v = b.toHilbert v := rfl

/-- Completion of a unit-modulus twist is the positive scalar twist on the
same actual Hilbert completion. -/
theorem twist_completedOperator (χ : G →* ℂˣ) (hχ : ∀ g, ‖(χ g : ℂ)‖ = 1)
    (g : G) (x : b.HilbertCompletion) :
    (b.twist χ hχ).completedOperator g x =
      (χ g : ℂ) • b.completedOperator g x := by
  refine b.denseRange_toHilbert.induction_on x ?_ ?_
  · exact isClosed_eq ((b.twist χ hχ).completedOperator g).continuous
      ((b.completedOperator g).continuous.const_smul (χ g : ℂ))
  · intro v
    exact ((b.twist χ hχ).completedOperator_toHilbert g v).trans
      ((b.toHilbert.map_smul (χ g : ℂ) (ρ g v)).trans
        (congrArg (fun y => (χ g : ℂ) • y) (b.completedOperator_toHilbert g v).symm))

/-- The representation-level compatibility retains the same completed carrier. -/
theorem twist_completedRepresentation (χ : G →* ℂˣ)
    (hχ : ∀ g, ‖(χ g : ℂ)‖ = 1) :
    (b.twist χ hχ).completedRepresentation = Langlands.twist χ b.completedRepresentation := by
  ext g x
  exact b.twist_completedOperator χ hχ g x

section TransportedForm

variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {σ : Representation ℂ G W} (e : ρ.Equiv σ)

/-- The original equivalence preserves the form transported by its inverse. -/
theorem ofEquiv_inner_apply (v w : V) :
    (b.ofEquiv e.symm).inner (e v) (e w) = b.inner v w := by
  change b.inner (e.symm (e v)) (e.symm (e w)) = _
  rw [e.symm_apply_apply, e.symm_apply_apply]

/-- Canonical completed equivalence when the target form is transported by the
inverse original equivalence. This specializes `completedEquiv` without an
additional form-preservation input. -/
def completedOfEquiv :
    b.HilbertCompletion ≃ₗᵢ[ℂ] (b.ofEquiv e.symm).HilbertCompletion :=
  b.completedEquiv (b.ofEquiv e.symm) e.toIntertwiningMap
    (b.ofEquiv_inner_apply e) e.toLinearEquiv.surjective

@[simp]
theorem completedOfEquiv_toHilbert (v : V) :
    b.completedOfEquiv e (b.toHilbert v) = (b.ofEquiv e.symm).toHilbert (e v) :=
  b.completedEquiv_toHilbert (b.ofEquiv e.symm) e.toIntertwiningMap
    (b.ofEquiv_inner_apply e) e.toLinearEquiv.surjective v

@[simp]
theorem completedOfEquiv_symm_toHilbert (w : W) :
    (b.completedOfEquiv e).symm ((b.ofEquiv e.symm).toHilbert w) =
      b.toHilbert (e.symm w) := by
  apply (b.completedOfEquiv e).injective
  rw [LinearIsometryEquiv.apply_symm_apply, completedOfEquiv_toHilbert, e.apply_symm_apply]

theorem completedOfEquiv_completedOperator (g : G) (x : b.HilbertCompletion) :
    b.completedOfEquiv e (b.completedOperator g x) =
      (b.ofEquiv e.symm).completedOperator g (b.completedOfEquiv e x) :=
  b.completedIsometry_completedOperator (b.ofEquiv e.symm) e.toIntertwiningMap
    (b.ofEquiv_inner_apply e) g x

/-- Additional covariance extends on the same transported-form completion,
provided both operators already extend continuously from the algebraic carriers. -/
theorem completedOfEquiv_covariant
    (a : Module.End ℂ V) (d : Module.End ℂ W)
    (A : b.HilbertCompletion →L[ℂ] b.HilbertCompletion)
    (D : (b.ofEquiv e.symm).HilbertCompletion →L[ℂ]
      (b.ofEquiv e.symm).HilbertCompletion)
    (hA : ∀ v, A (b.toHilbert v) = b.toHilbert (a v))
    (hD : ∀ w, D ((b.ofEquiv e.symm).toHilbert w) =
      (b.ofEquiv e.symm).toHilbert (d w))
    (hed : ∀ v, e (a v) = d (e v)) (x : b.HilbertCompletion) :
    b.completedOfEquiv e (A x) = D (b.completedOfEquiv e x) :=
  b.completedIsometry_covariant (b.ofEquiv e.symm) e.toIntertwiningMap
    (b.ofEquiv_inner_apply e) a d A D hA hD hed x

/-- Scalar covariance extends for any already continuous operators. -/
theorem completedOfEquiv_scalar_covariant
    (a : Module.End ℂ V) (d : Module.End ℂ W) (z : ℂ)
    (A : b.HilbertCompletion →L[ℂ] b.HilbertCompletion)
    (D : (b.ofEquiv e.symm).HilbertCompletion →L[ℂ]
      (b.ofEquiv e.symm).HilbertCompletion)
    (hA : ∀ v, A (b.toHilbert v) = b.toHilbert (a v))
    (hD : ∀ w, D ((b.ofEquiv e.symm).toHilbert w) =
      (b.ofEquiv e.symm).toHilbert (d w))
    (hed : ∀ v, d (e v) = z • e (a v)) (x : b.HilbertCompletion) :
    D (b.completedOfEquiv e x) = z • b.completedOfEquiv e (A x) :=
  (b.completedOfEquiv_covariant e (z • a) d (z • A) D
    (fun v => (congrArg (fun y => z • y) (hA v)).trans
      (b.toHilbert.map_smul z (a v)).symm)
    hD (fun v => (e.map_smul z (a v)).trans (hed v).symm) x).symm.trans
      ((b.completedOfEquiv e).map_smul z (A x))

end TransportedForm

section RestrictedEquiv

variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {σ : Representation ℂ H W}

/-- A restricted source intertwiner transports the original completed operator
at the actual homomorphism image. -/
theorem comp_completedOfEquiv_completedOperator
    (φ : H →* G) (e : Representation.Equiv (ρ.comp φ) σ)
    (h : H) (x : b.HilbertCompletion) :
    (b.comp φ).completedOfEquiv e (b.completedOperator (φ h) x) =
      ((b.comp φ).ofEquiv e.symm).completedOperator h
        ((b.comp φ).completedOfEquiv e x) :=
  (congrArg ((b.comp φ).completedOfEquiv e)
    (b.comp_completedOperator φ h x).symm).trans
      ((b.comp φ).completedOfEquiv_completedOperator e h x)

end RestrictedEquiv

section TwistedEquiv

variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {σ : Representation ℂ G W}

/-- An equivalence from a unit-modulus twist has the positive character
covariance on the unchanged source completion. -/
theorem twist_completedOfEquiv_completedOperator
    (χ : G →* ℂˣ) (hχ : ∀ g, ‖(χ g : ℂ)‖ = 1)
    (e : (Langlands.twist χ ρ).Equiv σ) (g : G) (x : b.HilbertCompletion) :
    ((b.twist χ hχ).ofEquiv e.symm).completedOperator g
        ((b.twist χ hχ).completedOfEquiv e x) =
      (χ g : ℂ) • (b.twist χ hχ).completedOfEquiv e (b.completedOperator g x) :=
  ((b.twist χ hχ).completedOfEquiv_completedOperator e g x).symm.trans
    ((congrArg ((b.twist χ hχ).completedOfEquiv e)
      (b.twist_completedOperator χ hχ g x)).trans
        (((b.twist χ hχ).completedOfEquiv e).map_smul (χ g : ℂ)
          (b.completedOperator g x)))

end TwistedEquiv

end Langlands.InvariantPositiveForm
