import Langlands.GroupScheme.Torus.Maximal
import Langlands.GroupScheme.Reductive.Basic

/-! # Statement: strongly regular points of a maximal torus over an algebraically closed field -/

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- **Strongly regular points of a maximal torus** (Steinberg, 2.15 and its proof). Let `G` be a
connected reductive group scheme over an algebraically closed field `k` and `j : T ⟶ G` a
maximal torus. Some nonempty open subset `U` of the underlying space of `T` consists of strongly
regular points: for every `k`-point `t` of `T` whose image lies in `U`, every point of `G` on any
test commuting with `t` factors through `T`. -/
def AlgClosedStronglyRegularTorusPointStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))) (j : T.toGrp ⟶ G),
      IsMaximalTorus j →
      ∃ U : Set T.X.left, IsOpen U ∧ U.Nonempty ∧
        ∀ t : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ T.X, Set.range t.left ⊆ U →
          ∀ {Z : Over (Spec (CommRingCat.of k))} (c : Z ⟶ G.X),
            c * (toUnit Z ≫ t ≫ j.hom.hom) = (toUnit Z ≫ t ≫ j.hom.hom) * c →
              ∃ s : Z ⟶ T.X, s ≫ j.hom.hom = c

end Langlands.GroupScheme
