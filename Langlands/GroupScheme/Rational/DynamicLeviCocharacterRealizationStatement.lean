import Langlands.GroupScheme.Dynamic.LeviParabolicDefinitions
import Langlands.GroupScheme.Reductive.Basic

/-! # Simultaneous dynamic realization of extension from a Levi -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- A cocharacter of a represented dynamic Levi extends to an ambient
cocharacter realizing its exact parabolic, centralizer and unipotent factors. -/
def DynamicLeviCocharacterRealizationStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
    ∀ (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
      (L : GroupScheme (Spec (CommRingCat.of k))) (j : L ⟶ G),
      IsClosedSubgroup j →
      ∀ hj : (Dynamic.centralizer χ).IsRepresentedBy j,
        ∀ ν : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ L,
          ∃ ψ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G,
            Dynamic.parabolic ψ =
                Dynamic.extendFromCentralizer χ j hj (Dynamic.parabolic ν) ∧
              Dynamic.centralizer ψ = (Dynamic.centralizer ν).map j ∧
              Dynamic.unipotent ψ =
                Dynamic.extendFromCentralizer χ j hj (Dynamic.unipotent ν)

end Langlands.GroupScheme
