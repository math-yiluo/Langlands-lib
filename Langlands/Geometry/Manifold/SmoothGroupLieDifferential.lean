import Langlands.Geometry.Manifold.SmoothGroupDifferential
import Langlands.Geometry.Manifold.VectorFieldCommutatorStatement

/-! # Reduction of the group differential commutator to manifold calculus -/

set_option autoImplicit false

noncomputable section

open scoped Classical Manifold ContDiff

namespace Langlands.Geometry.Manifold

set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G]

/-- The generic scalar commutator gives the bracket law for the unchanged
positive right-orbit derivative. -/
theorem groupDirectionalValue_commutator_of_vectorFieldCommutator
    (hcalc : smoothVectorFieldCommutator I G)
    (X Y : GroupLieAlgebra I G) {f : G → ℂ}
    (hf : ContMDiff I 𝓘(ℝ, ℂ) ∞ f) (g : G) :
    groupDirectionalValue I ⁅X, Y⁆ f g =
      groupDirectionalValue I X (groupDirectionalValue I Y f) g -
        groupDirectionalValue I Y (groupDirectionalValue I X f) g := by
  let : LieGroup I (minSmoothness ℝ 3) G :=
    LieGroup.of_le (n := ∞) (by simp)
  have hX : groupDirectionalValue I X f =
      fun x => mvfderiv I f x (mulInvariantVectorField X x) :=
    funext (groupDirectionalValue_eq_invariant I X hf)
  have hY : groupDirectionalValue I Y f =
      fun x => mvfderiv I f x (mulInvariantVectorField Y x) :=
    funext (groupDirectionalValue_eq_invariant I Y hf)
  rw [groupDirectionalValue_eq_invariant I ⁅X, Y⁆ hf,
    groupDirectionalValue_eq_invariant I X (contMDiff_groupDirectionalValue I Y hf),
    groupDirectionalValue_eq_invariant I Y (contMDiff_groupDirectionalValue I X hf),
    hX, hY, GroupLieAlgebra.bracket_def, mulInvariantVector_mlieBracket]
  exact hcalc (mulInvariantVectorField X) (mulInvariantVectorField Y)
    (mdifferentiable_mulInvariantVectorField X)
    (mdifferentiable_mulInvariantVectorField Y) f hf g

end Langlands.Geometry.Manifold
