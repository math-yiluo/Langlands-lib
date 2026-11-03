import Langlands.GroupScheme.Reductive.Semisimple
import Langlands.GroupScheme.Torus.LatticeGalois

/-! # Scheme-theoretic centre existence and field base change -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Every connected reductive group over a field has an actual closed subgroup
representing its full scheme-theoretic centre. -/
def SchemeTheoreticCenterExistenceStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
      ∃ (Z : GroupScheme (Spec (CommRingCat.of k))) (z : Z ⟶ G),
        IsSchemeTheoreticCenter z

/-- Every actual scheme-theoretic centre inclusion of a connected reductive group
remains such an inclusion after an arbitrary field extension. -/
def SchemeTheoreticCenterBaseChangeStatement : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
    (G Z : GroupScheme (Spec (CommRingCat.of k))) (z : Z ⟶ G),
    IsConnectedReductive G → IsSchemeTheoreticCenter z →
      IsSchemeTheoreticCenter ((GroupScheme.baseChange (algebraBaseMap k K)).map z)

end Langlands.GroupScheme
