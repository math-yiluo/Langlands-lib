import Langlands.GroupScheme.PseudoParabolic
import Langlands.GroupScheme.Reductive.Basic

/-! # Pseudo-reductive presentation of pseudo-parabolic quotients

This module states the reduction step of CGP Proposition C.1.6 through CGP
Proposition 2.2.10: a supplied homogeneous quotient of a smooth connected affine
group by a pseudo-parabolic subgroup is also a homogeneous quotient of a
pseudo-reductive group by an actual dynamic parabolic. It supplies no proof.
-/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Any supplied homogeneous quotient `q : G ⟶ Q` by a pseudo-parabolic
subgroup is presented by some pseudo-reductive group `G'` over the same field, an
actual cocharacter `χ` of `G'` and a smooth surjective quasi-compact map
`q' : G' ⟶ Q` whose all-test fibers are the right cosets of `P_{G'}(χ)`. -/
def PseudoParabolicQuotientPseudoReductiveReductionStatement : Prop :=
  ∀ (k : Type u) [Field k] (G P : GroupScheme (Spec (CommRingCat.of k)))
    (i : P ⟶ G),
    IsPseudoParabolicSubgroup i →
      ∀ (Q : Over (Spec (CommRingCat.of k))) (q : G.X ⟶ Q),
        Smooth q.left → Surjective q.left → QuasiCompact q.left →
        (∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G.X),
          g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range i).carrier T) →
        ∃ (G' : GroupScheme (Spec (CommRingCat.of k)))
          (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G') (q' : G'.X ⟶ Q),
          IsPseudoReductive G' ∧
            Smooth q'.left ∧ Surjective q'.left ∧ QuasiCompact q'.left ∧
            ∀ (T : Over (Spec (CommRingCat.of k))) (g h : T ⟶ G'.X),
              g ≫ q' = h ≫ q' ↔ g⁻¹ * h ∈ (Dynamic.parabolic χ).carrier T

end Langlands.GroupScheme
