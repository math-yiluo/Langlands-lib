import Langlands.Representation.Unitary.Completion
import Langlands.Representation.FiniteVectors
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.EMetricSpace.Lipschitz

/-! # Continuous completed actions from finite orbits and faithful evaluations -/

noncomputable section
universe uG uV uX
set_option autoImplicit false

namespace Langlands.InvariantPositiveForm

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {X : Type uX} {ρ : Representation ℂ G V}

/-- A finite algebraic orbit is continuous in any supplied invariant form norm
when faithful scalar evaluations of that orbit are continuous. -/
theorem continuous_normedOrbit_of_finite_evaluations
    (b : InvariantPositiveForm ρ) (I : V →ₗ[ℂ] (X → ℂ))
    (hI : Function.Injective I) (v : V)
    (hv : FiniteVectors.IsFiniteVector ρ v)
    (hcont : ∀ x : X, Continuous (fun g : G => I (ρ g v) x)) :
    Continuous (fun g : G => b.toNormedCarrier (ρ g v)) := by
  let P := (FiniteVectors.orbitSpan ρ v).map b.toNormedCarrier.toLinearMap
  let : Module.Finite ℂ (FiniteVectors.orbitSpan ρ v) := hv
  have : Module.Finite ℂ P := inferInstance
  let J : P →ₗ[ℂ] (X → ℂ) :=
    (I.comp b.toNormedCarrier.symm.toLinearMap).comp P.subtype
  have hJ : Function.Injective J := by
    intro x y h
    apply Subtype.ext
    exact b.toNormedCarrier.symm.injective (hI h)
  let o (g : G) : P :=
    ⟨b.toNormedCarrier (ρ g v),
      ⟨ρ g v, FiniteVectors.action_mem_orbitSpan ρ g v, rfl⟩⟩
  have ho : Continuous o := by
    apply (LinearMap.isClosedEmbedding_of_injective
      (LinearMap.ker_eq_bot.mpr hJ)).isEmbedding.continuous_iff.mpr
    apply continuous_pi
    intro x
    change Continuous (fun g : G => I (b.toNormedCarrier.symm
      (b.toNormedCarrier (ρ g v))) x)
    simpa only [LinearEquiv.symm_apply_apply] using hcont x
  exact continuous_subtype_val.comp ho

/-- Continuous embedded algebraic orbits extend to a jointly continuous action:
the embedded carrier is dense and every completed operator is an isometry. -/
theorem continuous_completedAction_of_embedded_orbits
    (b : InvariantPositiveForm ρ)
    (hcont : ∀ v : V, Continuous (fun g : G => b.toHilbert (ρ g v))) :
    Continuous (fun p : G × b.HilbertCompletion =>
      b.completedRepresentation p.1 p.2) := by
  apply continuous_prod_of_dense_continuous_lipschitzWith' _ 1
    b.denseRange_toHilbert
    (fun g => (b.completedOperator g).isometry.lipschitzWith)
  rintro _ ⟨v, rfl⟩
  simpa only [b.completedRepresentation_toHilbert] using hcont v

/-- The actual completed action, bundled as a continuous map, constructed from
finite algebraic orbits and continuous faithful scalar evaluations. -/
def completedContinuousActionOfFiniteEvaluations
    (b : InvariantPositiveForm ρ) (I : V →ₗ[ℂ] (X → ℂ))
    (hI : Function.Injective I)
    (hfinite : ∀ v : V, FiniteVectors.IsFiniteVector ρ v)
    (hcont : ∀ (v : V) (x : X), Continuous (fun g : G => I (ρ g v) x)) :
    C(G × b.HilbertCompletion, b.HilbertCompletion) where
  toFun p := b.completedRepresentation p.1 p.2
  continuous_toFun := b.continuous_completedAction_of_embedded_orbits (fun v => by
    change Continuous (fun g : G =>
      ((b.toNormedCarrier (ρ g v)) : b.HilbertCompletion))
    exact (UniformSpace.Completion.continuous_coe _).comp
      (b.continuous_normedOrbit_of_finite_evaluations I hI v (hfinite v) (hcont v)))

@[simp]
theorem completedContinuousActionOfFiniteEvaluations_apply
    (b : InvariantPositiveForm ρ) (I : V →ₗ[ℂ] (X → ℂ))
    (hI : Function.Injective I)
    (hfinite : ∀ v : V, FiniteVectors.IsFiniteVector ρ v)
    (hcont : ∀ (v : V) (x : X), Continuous (fun g : G => I (ρ g v) x))
    (g : G) (x : b.HilbertCompletion) :
    b.completedContinuousActionOfFiniteEvaluations I hI hfinite hcont (g, x) =
      b.completedRepresentation g x := rfl

end Langlands.InvariantPositiveForm
