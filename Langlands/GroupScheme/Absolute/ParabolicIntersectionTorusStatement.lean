import Langlands.GroupScheme.Absolute.Borel

/-! # A common rational maximal torus for two parabolic subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Borel–Tits, Proposition 4.7, first assertion: two rational parabolic
subgroups of a connected reductive group contain a common maximal torus
defined over the ground field. Containment is expressed by actual
homomorphisms of group schemes. -/
def ParabolicIntersectionTorusStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
    ∀ (P P' : GroupScheme (Spec (CommRingCat.of k))) (j : P ⟶ G) (j' : P' ⟶ G),
      IsParabolicSubgroup j → IsParabolicSubgroup j' →
      ∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
        (f : T.toGrp ⟶ P) (f' : T.toGrp ⟶ P'),
        IsMaximalTorus i ∧ f ≫ j = i ∧ f' ≫ j' = i

end Langlands.GroupScheme
