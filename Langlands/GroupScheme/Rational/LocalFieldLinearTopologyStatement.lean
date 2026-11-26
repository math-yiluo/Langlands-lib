import Langlands.Group.GL.AlgebraicPointTopology
import Langlands.GroupScheme.AffineLinearEmbeddingStatement
import Langlands.GroupScheme.Rational.Characters
import Langlands.AlgebraicGeometry.PointTopology.RationalPointEvaluation

/-! # Independence of the local-field rational-point topology from the linear embedding -/

universe u

open CategoryTheory AlgebraicGeometry Topology
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- A finite-type affine group is linear over a nonarchimedean local field.
Every closed linear embedding induces the canonical rational-point topology,
which is Hausdorff, locally compact, and totally disconnected. -/
def LocalFieldLinearTopologyStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom],
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    IsTopologicalGroup (rationalPoints G) ∧ T2Space (rationalPoints G) ∧
      LocallyCompactSpace (rationalPoints G) ∧ TotallyDisconnectedSpace (rationalPoints G) ∧
      (∃ (N : ℕ) (ρ : MatrixRepresentation G (Fin N)), IsClosedSubgroup ρ) ∧
      ∀ (N : ℕ) (ρ : MatrixRepresentation G (Fin N)), IsClosedSubgroup ρ →
        IsClosedEmbedding (fun g : rationalPoints G =>
          GeneralLinear.rationalPointsEquiv N (CommRingCat.of F) (rationalPoints.map ρ g))

end Langlands.GroupScheme
