import Langlands.GroupScheme.Absolute.Borel
import Langlands.GroupScheme.Dynamic.Basic

/-! # Normal unipotent subgroups of cocharacter centralizers and ambient Borels -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- A smooth connected normal unipotent subgroup of a represented cocharacter
centralizer lies in every ambient Borel containing the cocharacter. This is
the Borel-containment step in Milne 2017, Corollary 17.57. -/
def CentralizerUnipotentBorelContainmentStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (M : GroupScheme (Spec (CommRingCat.of k))) (j : M ⟶ G),
    IsClosedSubgroup j → (Dynamic.centralizer χ).IsRepresentedBy j →
    Smooth M.X.hom → ConnectedSpace M.X.left →
    ∀ (U : GroupScheme (Spec (CommRingCat.of k))) (i : U ⟶ M),
      IsClosedSubgroup i → Smooth U.X.hom → ConnectedSpace U.X.left → IsUnipotent U →
      (SubgroupFunctor.range i).IsNormal →
      ∀ (B : GroupScheme (Spec (CommRingCat.of k))) (b : B ⟶ G),
        IsBorelSubgroup b → SubgroupFunctor.range χ ≤ SubgroupFunctor.range b →
          SubgroupFunctor.range (i ≫ j) ≤ SubgroupFunctor.range b

end Langlands.GroupScheme
