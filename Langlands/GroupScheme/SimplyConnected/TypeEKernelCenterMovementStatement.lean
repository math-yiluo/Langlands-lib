import Langlands.GroupScheme.CenterMovingAutomorphisms
import Langlands.GroupScheme.SimplyConnected.TypeEAnisotropicKernelModel

/-! # The centre-moving anisotropic-kernel automorphism prerequisite -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- For an actual rank-one branch-marked E6 or E7 index with trivial full star,
there is an automorphism of its actual anisotropic kernel moving the full centre.
This geometric prerequisite is stated over arbitrary fields and is unproved. -/
def RankOneTypeEKernelCenterMovementStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G),
    IsSimplyConnected G → IsAbsolutelyAlmostSimple G → splitRank G = 1 →
    d.StarIsTrivial →
    ((∃ e : d.Vertex ≃ Fin 6,
      d.IsNumberingOf (CartanMatrix.E 6) (fun i => i.val = 1) e) ∨
     (∃ e : d.Vertex ≃ Fin 7,
      d.IsNumberingOf (CartanMatrix.E 7) (fun i => i.val = 1) e)) →
    HasCenterMovingAutomorphism d.anisotropicKernelIndex.kernel

end Langlands.GroupScheme
