import Langlands.GroupScheme.Dynamic.OppositeIntersection
import Langlands.GroupScheme.Reductive.Basic

/-! # Uniqueness of the opposite dynamic parabolic with a given Levi -/

universe u

open CategoryTheory
open _root_.AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Let `G` be a connected reductive group over a field `k` and let `χ`, `χ'` be cocharacters
of `G` with the same dynamic centralizer `Z(χ') = Z(χ)`. If the `k`-points of `P(χ)` and `P(χ')`
meet exactly in the `k`-points of `Z(χ)`, then `P(χ')` and `U(χ')` are the dynamic parabolic and
unipotent radical of the opposite cocharacter `χ⁻¹`. This is a proof target. -/
def OppositeDynamicParabolicUniquenessStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
    ∀ χ χ' : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G,
      Dynamic.centralizer χ' = Dynamic.centralizer χ →
      (Dynamic.parabolic χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) ⊓
          (Dynamic.parabolic χ').carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) =
        (Dynamic.centralizer χ).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) →
      Dynamic.parabolic χ' = Dynamic.parabolic (Dynamic.oppositeCocharacter χ) ∧
        Dynamic.unipotent χ' = Dynamic.unipotent (Dynamic.oppositeCocharacter χ)

end Langlands.GroupScheme
