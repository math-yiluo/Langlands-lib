import Langlands.GroupScheme.Dynamic.Basic
import Langlands.GroupScheme.Reductive.Basic

/-! # Connected reductivity of actual dynamic centralizers -/

universe u

open CategoryTheory
open _root_.AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Every closed group-scheme representative of the dynamic centralizer of a cocharacter
of a connected reductive group over a field is connected reductive. -/
def DynamicCentralizerReductiveStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
    ∀ (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
      (M : GroupScheme (Spec (CommRingCat.of k))) (j : M ⟶ G),
      IsClosedSubgroup j →
      (Dynamic.centralizer χ).IsRepresentedBy j →
      IsConnectedReductive M

end Langlands.GroupScheme
