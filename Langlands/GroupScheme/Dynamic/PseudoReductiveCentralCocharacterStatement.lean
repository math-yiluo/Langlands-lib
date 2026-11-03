import Langlands.GroupScheme.Dynamic.Basic
import Langlands.GroupScheme.Reductive.Basic

/-! # Full dynamic parabolics in pseudo-reductive groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Conrad--Gabber--Prasad, Lemma 2.2.3(2): the dynamic parabolic of a
cocharacter in a pseudo-reductive group is the whole group precisely when
the cocharacter centralizes the whole group, on every scheme test. -/
def PseudoReductiveCentralCocharacterStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsPseudoReductive G →
      ∀ χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G,
        Dynamic.parabolic χ = ⊤ ↔ Dynamic.centralizer χ = ⊤

end Langlands.GroupScheme
