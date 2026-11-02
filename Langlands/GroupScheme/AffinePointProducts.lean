import Langlands.GroupScheme.AffinePointFiniteCoordinates
import Mathlib.Algebra.Algebra.Prod

/-! # Actual affine group-scheme points over a product coefficient ring -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false

variable {R : CommRingCat.{u}} (G : GroupScheme (Spec R)) [IsAffine G.X.left]
  (A B : CommAlgCat.{u} R)

/-- The first coefficient projection on actual points. -/
def affinePointsFst : G.affinePoints (CommAlgCat.of R (A × B)) →* G.affinePoints A :=
  G.affinePointMap (CommAlgCat.ofHom (AlgHom.fst R A B))

/-- The second coefficient projection on actual points. -/
def affinePointsSnd : G.affinePoints (CommAlgCat.of R (A × B)) →* G.affinePoints B :=
  G.affinePointMap (CommAlgCat.ofHom (AlgHom.snd R A B))

/-- Pair two actual affine points by pairing their coordinate-algebra homomorphisms. -/
def affinePointPair (x : G.affinePoints A) (y : G.affinePoints B) :
    G.affinePoints (CommAlgCat.of R (A × B)) :=
  (affineSchemePointEquiv R G.X (A × B)).symm
    (AlgPoint.ofAlgHom ((affineSchemePointEquiv R G.X A x).toAlgHom.prod
      (affineSchemePointEquiv R G.X B y).toAlgHom))

@[simp]
theorem affinePointPair_evaluation (x : G.affinePoints A) (y : G.affinePoints B)
    (a : Γ(G.X.left, ⊤)) :
    G.affinePointEvaluation (CommAlgCat.of R (A × B)) (G.affinePointPair A B x y) a =
      (G.affinePointEvaluation A x a, G.affinePointEvaluation B y a) := by
  rw [← G.affineSchemePointEquiv_evaluation]
  change (affineSchemePointEquiv R G.X (A × B))
    ((affineSchemePointEquiv R G.X (A × B)).symm _) a = _
  rw [Equiv.apply_symm_apply]
  change ((affineSchemePointEquiv R G.X A x) a,
    (affineSchemePointEquiv R G.X B y) a) = _
  rw [G.affineSchemePointEquiv_evaluation, G.affineSchemePointEquiv_evaluation]

@[simp]
theorem affinePointsFst_pair (x : G.affinePoints A) (y : G.affinePoints B) :
    G.affinePointsFst A B (G.affinePointPair A B x y) = x := by
  apply G.affinePointEvaluation_injective A
  funext a
  dsimp only [affinePointsFst]
  rw [G.affinePointEvaluation_map, G.affinePointPair_evaluation]
  rfl

@[simp]
theorem affinePointsSnd_pair (x : G.affinePoints A) (y : G.affinePoints B) :
    G.affinePointsSnd A B (G.affinePointPair A B x y) = y := by
  apply G.affinePointEvaluation_injective B
  funext a
  dsimp only [affinePointsSnd]
  rw [G.affinePointEvaluation_map, G.affinePointPair_evaluation]
  rfl

@[simp]
theorem affinePointPair_projections (x : G.affinePoints (CommAlgCat.of R (A × B))) :
    G.affinePointPair A B (G.affinePointsFst A B x) (G.affinePointsSnd A B x) = x := by
  apply G.affinePointEvaluation_injective (CommAlgCat.of R (A × B))
  funext a
  change G.affinePointEvaluation (CommAlgCat.of R (A × B))
    (G.affinePointPair A B (G.affinePointsFst A B x) (G.affinePointsSnd A B x)) a =
      G.affinePointEvaluation (CommAlgCat.of R (A × B)) x a
  rw [G.affinePointPair_evaluation]
  dsimp only [affinePointsFst, affinePointsSnd]
  rw [G.affinePointEvaluation_map, G.affinePointEvaluation_map]
  rfl

/-- Product coefficients give the product of the actual affine point groups. -/
def affinePointsProdEquiv :
    G.affinePoints (CommAlgCat.of R (A × B)) ≃* (G.affinePoints A × G.affinePoints B) where
  toFun x := (G.affinePointsFst A B x, G.affinePointsSnd A B x)
  invFun p := G.affinePointPair A B p.1 p.2
  left_inv := G.affinePointPair_projections A B
  right_inv p := by simp
  map_mul' x y := Prod.ext ((G.affinePointsFst A B).map_mul x y)
    ((G.affinePointsSnd A B).map_mul x y)

variable [TopologicalSpace A] [TopologicalSpace B]

/-- Both coefficient projections are continuous in the existing evaluation topologies. -/
theorem continuous_affinePointsProdEquiv : Continuous (G.affinePointsProdEquiv A B) :=
  (G.continuous_affinePointMap (CommAlgCat.ofHom (AlgHom.fst R A B)) continuous_fst).prodMk
    (G.continuous_affinePointMap (CommAlgCat.ofHom (AlgHom.snd R A B)) continuous_snd)

/-- Coordinatewise pairing is continuous for arbitrary topological coefficient rings. -/
theorem continuous_affinePointPair :
    Continuous (fun p : G.affinePoints A × G.affinePoints B =>
      G.affinePointPair A B p.1 p.2) := by
  apply (G.continuous_affinePoints_iff (CommAlgCat.of R (A × B)) _).mpr
  intro a
  simp_rw [G.affinePointPair_evaluation]
  exact ((G.continuous_affinePointEvaluation A a).comp continuous_fst).prodMk
    ((G.continuous_affinePointEvaluation B a).comp continuous_snd)

/-- The product-coefficient decomposition preserves the actual evaluation topology. -/
def affinePointsProdHomeomorph :
    G.affinePoints (CommAlgCat.of R (A × B)) ≃ₜ* (G.affinePoints A × G.affinePoints B) where
  toMulEquiv := G.affinePointsProdEquiv A B
  continuous_toFun := G.continuous_affinePointsProdEquiv A B
  continuous_invFun := G.continuous_affinePointPair A B

end Langlands.GroupScheme
