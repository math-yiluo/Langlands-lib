import Langlands.AbelianScheme.HomLocalLatticeStatement
import Langlands.AbelianScheme.HomPullbackMixedEulerCube
import Langlands.AbelianScheme.HomPullbackMixedEulerPositive
import Langlands.AbelianScheme.FieldAmpleExistenceProof
import Langlands.AlgebraicGeometry.SmoothConnectedRelativeDimensionProof
import Langlands.AlgebraicGeometry.Picard.RosatiZeroDimension

/-! # Integral Hom in finite-dimensional rational subspaces -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

/-- Integral homomorphisms in any finitely generated rational Hom subspace
form a finitely generated integer module. -/
theorem homLocalLattice : HomLocalLatticeStatement.{u} := by
  intro k _ _ _ A B V hV
  have : ConnectedSpace A.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton A.X.hom
  obtain ⟨g, hg⟩ := Langlands.AlgebraicGeometry.smoothConnectedRelativeDimension _ _
    A.X.hom inferInstance inferInstance
  cases g with
  | zero =>
      have : Subsingleton (A ⟶ B) :=
        ⟨fun f f' => (hom_eq_zero_of_relativeDimension_zero hg f).trans
          (hom_eq_zero_of_relativeDimension_zero hg f').symm⟩
      have : IsNoetherian ℤ (A ⟶ B) := isNoetherian_of_isNoetherianRing_of_finite ℤ (A ⟶ B)
      exact IsNoetherian.noetherian _
  | succ d =>
      obtain ⟨LA, hLA⟩ := GroupScheme.fieldAmpleExistence k A.toGrp inferInstance
        inferInstance inferInstance
      obtain ⟨LB, hLB⟩ := GroupScheme.fieldAmpleExistence k B.toGrp inferInstance
        inferInstance inferInstance
      exact fg_comap_homToHom0_of_homMixedEuler_pos LA LB d hg
        (fun f hf => mixedLineBundleEulerCoefficient_pullback_pos_of_ne_zero (d + 1)
          (Nat.succ_pos d) hg LA hLA LB hLB f hf) V hV

end Langlands.AbelianScheme
