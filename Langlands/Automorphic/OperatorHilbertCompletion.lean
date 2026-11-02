import Langlands.Automorphic.OperatorUnitaryForm
import Langlands.Automorphic.OperatorCompactCompatibility
import Langlands.Representation.Unitary.Completion
import Mathlib.Topology.EMetricSpace.Lipschitz

/-! # A common Hilbert completion of actual finite and compact actions -/

noncomputable section
universe uF uV uG uK uX
set_option autoImplicit false
set_option maxHeartbeats 20000

namespace Langlands.Automorphic

namespace OperatorUnitaryFormCore

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {G : Type uG} [Group G] {K : Type uK} [Group K] {X : Type uX}
  {ρ : Representation ℂ G V} {κ : Representation ℂ K V} {D : X → Module.End ℂ V}

/-- The second action preserves exactly the first action's positive core. -/
def compactInvariantForm (b : OperatorUnitaryFormCore ρ κ D) :
    Langlands.InvariantPositiveForm κ where
  toInnerProductCore := b.finiteForm.toInnerProductCore
  invariant := b.compact_invariant

/-- The actual completion for the single supplied positive form. -/
abbrev HilbertCompletion (b : OperatorUnitaryFormCore ρ κ D) := b.finiteForm.HilbertCompletion

/-- The actual algebraic form carrier embeds into its form-dependent completion. -/
def toHilbert (b : OperatorUnitaryFormCore ρ κ D) : V →ₗ[ℂ] b.HilbertCompletion :=
  b.finiteForm.toHilbert

theorem toHilbert_injective (b : OperatorUnitaryFormCore ρ κ D) : Function.Injective b.toHilbert :=
  b.finiteForm.toHilbert_injective

theorem denseRange_toHilbert (b : OperatorUnitaryFormCore ρ κ D) : DenseRange b.toHilbert :=
  b.finiteForm.denseRange_toHilbert

@[simp] theorem inner_toHilbert (b : OperatorUnitaryFormCore ρ κ D) (f g : V) :
    Inner.inner ℂ (b.toHilbert f) (b.toHilbert g) = b.finiteForm.inner f g :=
  b.finiteForm.inner_toHilbert f g

theorem norm_toHilbert (b : OperatorUnitaryFormCore ρ κ D) (f : V) :
    ‖b.toHilbert f‖ = Real.sqrt (b.finiteForm.inner f f).re :=
  b.finiteForm.norm_toHilbert f

/-- Extension of actual finite translation as an isometric equivalence. -/
def completedFiniteOperator (b : OperatorUnitaryFormCore ρ κ D) (d : G) :
    b.HilbertCompletion ≃ₗᵢ[ℂ] b.HilbertCompletion :=
  b.finiteForm.completedOperator d

/-- Compact translation extends on the SAME completion: `compactForm` retains
exactly the positive core of `finiteForm`. -/
def completedCompactOperator (b : OperatorUnitaryFormCore ρ κ D) (k : K) :
    b.HilbertCompletion ≃ₗᵢ[ℂ] b.HilbertCompletion :=
  b.compactInvariantForm.completedOperator k

@[simp] theorem completedFiniteOperator_toHilbert (b : OperatorUnitaryFormCore ρ κ D)
    (d : G) (f : V) :
    b.completedFiniteOperator d (b.toHilbert f) =
      b.toHilbert (ρ d f) :=
  b.finiteForm.completedOperator_toHilbert d f

@[simp] theorem completedCompactOperator_toHilbert (b : OperatorUnitaryFormCore ρ κ D)
    (k : K) (f : V) :
    b.completedCompactOperator k (b.toHilbert f) =
      b.toHilbert (κ k f) :=
  b.compactInvariantForm.completedOperator_toHilbert k f

@[simp] theorem completedFiniteOperator_symm (b : OperatorUnitaryFormCore ρ κ D)
    (d : G) :
    (b.completedFiniteOperator d).symm = b.completedFiniteOperator d⁻¹ :=
  b.finiteForm.completedOperator_symm d

@[simp] theorem completedCompactOperator_symm (b : OperatorUnitaryFormCore ρ κ D)
    (k : K) :
    (b.completedCompactOperator k).symm = b.completedCompactOperator k⁻¹ :=
  b.compactInvariantForm.completedOperator_symm k

/-- The finite representation on the common actual Hilbert space. -/
def completedFiniteRepresentation (b : OperatorUnitaryFormCore ρ κ D) :
    Representation ℂ (G) b.HilbertCompletion :=
  b.finiteForm.completedRepresentation

/-- The compact representation on the very same actual Hilbert space. -/
def completedCompactRepresentation (b : OperatorUnitaryFormCore ρ κ D) :
    Representation ℂ (K) b.HilbertCompletion :=
  b.compactInvariantForm.completedRepresentation

theorem completedFiniteRepresentation_apply (b : OperatorUnitaryFormCore ρ κ D)
    (d : G) (x : b.HilbertCompletion) :
    b.completedFiniteRepresentation d x = b.completedFiniteOperator d x := rfl

theorem completedCompactRepresentation_apply (b : OperatorUnitaryFormCore ρ κ D)
    (k : K) (x : b.HilbertCompletion) :
    b.completedCompactRepresentation k x = b.completedCompactOperator k x := rfl

@[simp] theorem completedFiniteRepresentation_toHilbert (b : OperatorUnitaryFormCore ρ κ D)
    (d : G) (f : V) :
    b.completedFiniteRepresentation d (b.toHilbert f) =
      b.toHilbert (ρ d f) :=
  b.completedFiniteOperator_toHilbert d f

@[simp] theorem completedCompactRepresentation_toHilbert (b : OperatorUnitaryFormCore ρ κ D)
    (k : K) (f : V) :
    b.completedCompactRepresentation k (b.toHilbert f) =
      b.toHilbert (κ k f) :=
  b.completedCompactOperator_toHilbert k f

/-- The two actual translations still commute after completion. -/
theorem completedFiniteOperator_compactOperator (b : OperatorUnitaryFormCore ρ κ D)
    (hρκ : ∀ (d : G) (k : K) (f : V), ρ d (κ k f) = κ k (ρ d f))
    (d : G) (k : K) (x : b.HilbertCompletion) :
    b.completedFiniteOperator d (b.completedCompactOperator k x) =
      b.completedCompactOperator k (b.completedFiniteOperator d x) := by
  refine b.denseRange_toHilbert.induction_on x ?_ ?_
  · exact isClosed_eq
      ((b.completedFiniteOperator d).continuous.comp (b.completedCompactOperator k).continuous)
      ((b.completedCompactOperator k).continuous.comp (b.completedFiniteOperator d).continuous)
  · intro f
    have h₁ : b.completedFiniteOperator d (b.completedCompactOperator k (b.toHilbert f)) =
        b.completedFiniteOperator d (b.toHilbert (κ k f)) :=
      congrArg (b.completedFiniteOperator d) (b.completedCompactOperator_toHilbert k f)
    have h₂ : b.completedFiniteOperator d (b.toHilbert (κ k f)) =
        b.toHilbert (ρ d (κ k f)) :=
      b.completedFiniteOperator_toHilbert d (κ k f)
    have h₃ : b.toHilbert (ρ d (κ k f)) =
        b.toHilbert (κ k (ρ d f)) :=
      congrArg b.toHilbert (hρκ d k f)
    have h₄ : b.completedCompactOperator k (b.toHilbert (ρ d f)) =
        b.toHilbert (κ k (ρ d f)) :=
      b.completedCompactOperator_toHilbert k (ρ d f)
    have h₅ : b.completedCompactOperator k (b.completedFiniteOperator d (b.toHilbert f)) =
        b.completedCompactOperator k (b.toHilbert (ρ d f)) :=
      congrArg (b.completedCompactOperator k) (b.completedFiniteOperator_toHilbert d f)
    exact h₁.trans (h₂.trans (h₃.trans (h₄.symm.trans h₅.symm)))

theorem completedFiniteRepresentation_compactRepresentation (b : OperatorUnitaryFormCore ρ κ D)
    (hρκ : ∀ (d : G) (k : K) (f : V), ρ d (κ k f) = κ k (ρ d f))
    (d : G) (k : K) (x : b.HilbertCompletion) :
    b.completedFiniteRepresentation d (b.completedCompactRepresentation k x) =
      b.completedCompactRepresentation k (b.completedFiniteRepresentation d x) :=
  b.completedFiniteOperator_compactOperator hρκ d k x

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- Smoothness gives continuous completed orbits. -/
theorem continuous_completedFiniteOrbit (b : OperatorUnitaryFormCore ρ κ D) (hρ : Langlands.IsSmooth ρ)
    (x : b.HilbertCompletion) :
    Continuous (fun d : G => b.completedFiniteRepresentation d x) :=
  b.finiteForm.continuous_completedOrbit hρ x

/-- The completed finite action is jointly continuous in group and Hilbert vector. -/
theorem continuous_completedFiniteAction (b : OperatorUnitaryFormCore ρ κ D)
    (hρ : Langlands.IsSmooth ρ) :
    Continuous (fun p : G × b.HilbertCompletion =>
      b.completedFiniteRepresentation p.1 p.2) :=
  continuous_prod_of_continuous_lipschitzWith' _ 1
    (fun d => (b.completedFiniteOperator d).isometry.lipschitzWith)
    (b.continuous_completedFiniteOrbit hρ)

end OperatorUnitaryFormCore

open Langlands.Global

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}

local instance hilbertRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance hilbertContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance hilbertSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance hilbertFormsGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance hilbertStableGroup : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _

namespace OperatorRealization.UnitaryForm

variable {S : OperatorRealization F n}

local instance hilbertSpaceGroup : AddCommGroup S.Space := Submodule.addCommGroup _

/-- The actual Hilbert space associated to the single supplied positive form. -/
abbrev HilbertCompletion (b : S.UnitaryForm) := OperatorUnitaryFormCore.HilbertCompletion b

end OperatorRealization.UnitaryForm
end Langlands.Automorphic
