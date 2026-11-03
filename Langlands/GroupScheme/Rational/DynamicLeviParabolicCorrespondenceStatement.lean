import Langlands.GroupScheme.Dynamic.LeviParabolicDefinitions
import Langlands.GroupScheme.Reductive.Basic

/-! # Actual parabolics in a represented dynamic Levi -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Parabolics of a represented dynamic Levi correspond, by exact extension
and inverse image, to ambient parabolics contained in its dynamic parabolic. -/
def DynamicLeviParabolicCorrespondenceStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
    ∀ (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
      (L : GroupScheme (Spec (CommRingCat.of k))) (j : L ⟶ G),
      IsClosedSubgroup j →
      ∀ hj : (Dynamic.centralizer χ).IsRepresentedBy j,
        ∃ e : ParabolicFunctor L ≃o ParabolicFunctorBelow (Dynamic.parabolic χ),
          (∀ F : ParabolicFunctor L,
            (e F).val = Dynamic.extendFromCentralizer χ j hj F.val) ∧
          (∀ Q : ParabolicFunctorBelow (Dynamic.parabolic χ),
            (e.symm Q).val = Q.val.comap j)

end Langlands.GroupScheme
