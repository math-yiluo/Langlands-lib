import Langlands.GroupScheme.Absolute.Borel
import Langlands.GroupScheme.Reductive.RootDatum
import Langlands.GroupScheme.Dynamic.Basic

/-! # Statement: the two dynamic Borels in semisimple rank one -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- In semisimple rank one, a Borel through a split maximal torus is one of
the two opposite dynamic parabolics defined by any cocharacter nonorthogonal
to a root. This is a derived form of Milne 2017, Lemma 20.20. -/
def RankOneBorelDynamicStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (j : T.toGrp ⟶ G),
    IsSplitTorus T.toGrp → IsMaximalTorus j →
      haveI := hG.isAffineHom
      (∀ α ∈ roots j, ∀ β ∈ roots j, ¬ LinearIndependent ℤ ![α, β]) →
      ∀ α ∈ roots j, ∀ ν : cocharacterLattice T, latticePairing T α ν ≠ 0 →
        ∀ (B : GroupScheme (Spec (CommRingCat.of k))) (b : B ⟶ G)
          (t : T.toGrp ⟶ B), IsBorelSubgroup b → t ≫ b = j →
          (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ j)).IsRepresentedBy b ∨
          (Dynamic.parabolic (CommGroupScheme.groupHom (-ν) ≫ j)).IsRepresentedBy b

end Langlands.GroupScheme
