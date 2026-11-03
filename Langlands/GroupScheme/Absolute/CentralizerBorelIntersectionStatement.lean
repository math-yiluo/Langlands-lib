import Langlands.GroupScheme.Absolute.Borel
import Langlands.GroupScheme.Dynamic.Basic

/-! # Borel subgroups of cocharacter centralizers inside ambient Borels -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- A Borel subgroup of the ambient group containing a cocharacter contains a Borel subgroup
of a represented centralizer of that cocharacter. This is the existence half of
Milne 2017, Theorem 17.46, for the image of the cocharacter. -/
def CentralizerBorelIntersectionStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (M : GroupScheme (Spec (CommRingCat.of k))) (j : M ⟶ G),
    IsClosedSubgroup j → (Dynamic.centralizer χ).IsRepresentedBy j →
    Smooth M.X.hom → ConnectedSpace M.X.left →
    ∀ (B : GroupScheme (Spec (CommRingCat.of k))) (b : B ⟶ G),
      IsBorelSubgroup b → SubgroupFunctor.range χ ≤ SubgroupFunctor.range b →
        ∃ (C : GroupScheme (Spec (CommRingCat.of k))) (c : C ⟶ M),
          IsBorelSubgroup c ∧ SubgroupFunctor.range (c ≫ j) ≤ SubgroupFunctor.range b

end Langlands.GroupScheme
