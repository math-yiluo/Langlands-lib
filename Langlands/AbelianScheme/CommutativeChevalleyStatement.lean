import Langlands.AbelianScheme.Basic
import Langlands.GroupScheme.Torus.KernelCocharacters

/-! # Chevalley's theorem for commutative groups over algebraically closed fields -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

/-- A smooth connected commutative algebraic group over an algebraically closed
field admits an abelian variety quotient with smooth connected affine kernel. -/
def CommutativeChevalleyStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (G : CommGroupScheme (Spec (CommRingCat.of k))),
    Smooth G.X.hom → QuasiCompact G.X.hom → ConnectedSpace G.X.left →
    ∃ (A : AbelianScheme (Spec (CommRingCat.of k))) (q : G ⟶ A.toCommGroupScheme),
      Smooth (CommGroupScheme.hom q) ∧ Surjective (CommGroupScheme.hom q) ∧
      Smooth (CommGroupScheme.kernel q).X.hom ∧
      IsAffineHom (CommGroupScheme.kernel q).X.hom ∧
      ConnectedSpace (CommGroupScheme.kernel q).X.left

end Langlands.AbelianScheme
