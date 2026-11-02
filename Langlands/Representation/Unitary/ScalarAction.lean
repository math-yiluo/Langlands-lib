import Langlands.Representation.Unitary.Completion
import Langlands.Representation.Unitary.Twist

/-! # Scalar actions on an unchanged form-dependent Hilbert completion -/

noncomputable section
set_option autoImplicit false

namespace Langlands

universe uG uH uV

/-- A scalar-coordinate formula determines an operator on the whole carrier. -/
theorem operator_eq_smul_of_scalarEquiv
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (e : ℂ ≃ₗ[ℂ] V) (a : Module.End ℂ V) (z : ℂ)
    (ha : ∀ c, a (e c) = e (z * c)) (v : V) :
    a v = z • v := by
  obtain ⟨c, rfl⟩ := e.surjective v
  exact (ha c).trans (e.map_smul z c)

/-- Scalar coordinates of character-valued functions identify the scalar action
with positive right translation. No topology or evaluation bound is needed. -/
theorem scalarEquiv_right_translation
    {H : Type uH} [Group H]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (e : ℂ ≃ₗ[ℂ] V) (j : V → H → ℂ) (θ : H →* ℂˣ)
    (hj : ∀ c h, j (e c) h = (θ h : ℂ) * c)
    (g x : H) (v : V) :
    j ((θ g : ℂ) • v) x = j v (x * g) := by
  obtain ⟨c, rfl⟩ := e.surjective v
  rw [← e.map_smul, hj, hj, map_mul, Units.val_mul, smul_eq_mul]
  ac_rfl

namespace InvariantPositiveForm

variable {G : Type uG} [Group G]
  {H : Type uH} [Group H]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ G V}
  (b : InvariantPositiveForm ρ)

private def trivialActionForm :
    InvariantPositiveForm (Representation.trivial ℂ H V) where
  toInnerProductCore := b.toInnerProductCore
  invariant _ _ _ := rfl

/-- A unit-modulus scalar action preserves the exact original positive core. -/
def scalarActionForm (θ : H →* ℂˣ) (hθ : ∀ h, ‖(θ h : ℂ)‖ = 1) :
    InvariantPositiveForm (Langlands.twist θ (Representation.trivial ℂ H V)) :=
  (trivialActionForm (H := H) b).twist θ hθ

@[simp]
theorem scalarActionForm_inner (θ : H →* ℂˣ) (hθ : ∀ h, ‖(θ h : ℂ)‖ = 1)
    (v w : V) :
    (b.scalarActionForm θ hθ).inner v w = b.inner v w := rfl

@[simp]
theorem scalarActionForm_toHilbert (θ : H →* ℂˣ) (hθ : ∀ h, ‖(θ h : ℂ)‖ = 1)
    (v : V) :
    (b.scalarActionForm θ hθ).toHilbert v = b.toHilbert v := rfl

/-- A scalar original operator extends to the same scalar on the actual completion. -/
theorem completedOperator_eq_smul (g : G) (z : ℂ)
    (hρ : ∀ v, ρ g v = z • v) (x : b.HilbertCompletion) :
    b.completedOperator g x = z • x := by
  refine b.denseRange_toHilbert.induction_on x ?_ ?_
  · exact isClosed_eq (b.completedOperator g).continuous
      (continuous_const_smul z)
  · intro v
    rw [completedOperator_toHilbert, hρ, map_smul]

@[simp]
theorem scalarActionForm_completedOperator
    (θ : H →* ℂˣ) (hθ : ∀ h, ‖(θ h : ℂ)‖ = 1)
    (h : H) (x : b.HilbertCompletion) :
    (b.scalarActionForm θ hθ).completedOperator h x = (θ h : ℂ) • x :=
  (b.scalarActionForm θ hθ).completedOperator_eq_smul h (θ h : ℂ) (fun _ => rfl) x

/-- The completed scalar representation is jointly continuous for any topology
on the group making its complex-valued character continuous. -/
def scalarContinuousAction [TopologicalSpace H]
    (θ : H →* ℂˣ) (hθ : ∀ h, ‖(θ h : ℂ)‖ = 1)
    (hc : Continuous (fun h => (θ h : ℂ))) :
    C(H × b.HilbertCompletion, b.HilbertCompletion) where
  toFun p := (b.scalarActionForm θ hθ).completedRepresentation p.1 p.2
  continuous_toFun := by
    have heq :
        (fun p : H × b.HilbertCompletion =>
          (b.scalarActionForm θ hθ).completedRepresentation p.1 p.2) =
          (fun p => (θ p.1 : ℂ) • p.2) := by
      funext p
      exact b.scalarActionForm_completedOperator θ hθ p.1 p.2
    rw [heq]
    exact (hc.comp continuous_fst).smul continuous_snd

@[simp]
theorem scalarContinuousAction_apply [TopologicalSpace H]
    (θ : H →* ℂˣ) (hθ : ∀ h, ‖(θ h : ℂ)‖ = 1)
    (hc : Continuous (fun h => (θ h : ℂ))) (h : H) (x : b.HilbertCompletion) :
    b.scalarContinuousAction θ hθ hc (h, x) = (θ h : ℂ) • x :=
  b.scalarActionForm_completedOperator θ hθ h x

end InvariantPositiveForm
end Langlands
