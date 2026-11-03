import Langlands.GroupScheme.AffinePointFiniteCoordinates
import Mathlib.Algebra.Algebra.Pi

/-! # Actual affine group-scheme points over a family of coefficient rings -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false

variable {R : CommRingCat.{u}} (G : GroupScheme (Spec R)) [IsAffine G.X.left]
  {J : Type u} (A : J → CommAlgCat.{u} R)

/-- The coefficient projection at an index, acting on actual group-scheme points. -/
def affinePointsEval (i : J) :
    G.affinePoints (CommAlgCat.of R ((i : J) → A i)) →* G.affinePoints (A i) :=
  G.affinePointMap (CommAlgCat.ofHom (Pi.evalAlgHom R (fun i => A i) i))

/-- Assemble actual points by assembling their coordinate-algebra homomorphisms. -/
def affinePointPi (x : (i : J) → G.affinePoints (A i)) :
    G.affinePoints (CommAlgCat.of R ((i : J) → A i)) :=
  (affineSchemePointEquiv R G.X ((i : J) → A i)).symm
    (AlgPoint.ofAlgHom (AlgHom.pi
      (fun i => (affineSchemePointEquiv R G.X (A i) (x i)).toAlgHom)))

@[simp]
theorem affinePointPi_evaluation (x : (i : J) → G.affinePoints (A i))
    (a : Γ(G.X.left, ⊤)) (i : J) :
    G.affinePointEvaluation (CommAlgCat.of R ((i : J) → A i)) (G.affinePointPi A x) a i =
      G.affinePointEvaluation (A i) (x i) a := by
  rw [← G.affineSchemePointEquiv_evaluation]
  change (affineSchemePointEquiv R G.X ((i : J) → A i))
    ((affineSchemePointEquiv R G.X ((i : J) → A i)).symm _) a i = _
  rw [Equiv.apply_symm_apply]
  exact G.affineSchemePointEquiv_evaluation (A i) (x i) a

omit [IsAffine G.X.left] in
@[simp]
theorem affinePointsEval_evaluation
    (x : G.affinePoints (CommAlgCat.of R ((i : J) → A i)))
    (a : Γ(G.X.left, ⊤)) (i : J) :
    G.affinePointEvaluation (A i) (G.affinePointsEval A i x) a =
      G.affinePointEvaluation (CommAlgCat.of R ((i : J) → A i)) x a i := by
  dsimp only [affinePointsEval]
  rw [G.affinePointEvaluation_map]
  rfl

@[simp]
theorem affinePointsEval_pi (x : (i : J) → G.affinePoints (A i)) (i : J) :
    G.affinePointsEval A i (G.affinePointPi A x) = x i := by
  apply G.affinePointEvaluation_injective (A i)
  funext a
  change G.affinePointEvaluation (A i) (G.affinePointsEval A i (G.affinePointPi A x)) a =
    G.affinePointEvaluation (A i) (x i) a
  rw [G.affinePointsEval_evaluation, G.affinePointPi_evaluation]

@[simp]
theorem affinePointPi_evaluations
    (x : G.affinePoints (CommAlgCat.of R ((i : J) → A i))) :
    G.affinePointPi A (fun i => G.affinePointsEval A i x) = x := by
  apply G.affinePointEvaluation_injective (CommAlgCat.of R ((i : J) → A i))
  funext a i
  change G.affinePointEvaluation (CommAlgCat.of R ((i : J) → A i))
      (G.affinePointPi A (fun i => G.affinePointsEval A i x)) a i =
    G.affinePointEvaluation (CommAlgCat.of R ((i : J) → A i)) x a i
  rw [G.affinePointPi_evaluation, G.affinePointsEval_evaluation]

/-- Points over a dependent product of coefficient algebras form the product of
the original point groups, including for an empty indexing type. -/
def affinePointsPiEquiv :
    G.affinePoints (CommAlgCat.of R ((i : J) → A i)) ≃*
      ((i : J) → G.affinePoints (A i)) where
  toFun x i := G.affinePointsEval A i x
  invFun := G.affinePointPi A
  left_inv := G.affinePointPi_evaluations A
  right_inv x := funext (G.affinePointsEval_pi A x)
  map_mul' x y := funext (fun i => (G.affinePointsEval A i).map_mul x y)

@[simp]
theorem affinePointsPiEquiv_apply
    (x : G.affinePoints (CommAlgCat.of R ((i : J) → A i))) (i : J) :
    G.affinePointsPiEquiv A x i = G.affinePointsEval A i x := rfl

variable [∀ i, TopologicalSpace (A i)]

/-- All coefficient projections are continuous in the existing evaluation topologies. -/
theorem continuous_affinePointsPiEquiv : Continuous (G.affinePointsPiEquiv A) := by
  apply continuous_pi
  intro i
  exact G.continuous_affinePointMap
    (CommAlgCat.ofHom (Pi.evalAlgHom R (fun i => A i) i)) (continuous_apply i)

/-- Assembly of a family of actual points is continuous for product topologies. -/
theorem continuous_affinePointPi : Continuous (G.affinePointPi A) := by
  apply (G.continuous_affinePoints_iff (CommAlgCat.of R ((i : J) → A i)) _).mpr
  intro a
  apply continuous_pi
  intro i
  simp_rw [G.affinePointPi_evaluation]
  exact (G.continuous_affinePointEvaluation (A i) a).comp (continuous_apply i)

/-- The dependent coefficient-product decomposition preserves the actual group
structures and the original regular-function evaluation topologies. -/
def affinePointsPiHomeomorph :
    G.affinePoints (CommAlgCat.of R ((i : J) → A i)) ≃ₜ*
      ((i : J) → G.affinePoints (A i)) where
  toMulEquiv := G.affinePointsPiEquiv A
  continuous_toFun := G.continuous_affinePointsPiEquiv A
  continuous_invFun := G.continuous_affinePointPi A

end Langlands.GroupScheme
