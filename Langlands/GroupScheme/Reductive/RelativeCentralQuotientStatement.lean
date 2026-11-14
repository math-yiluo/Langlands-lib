import Langlands.GroupScheme.Dynamic.Functoriality
import Langlands.GroupScheme.Rational.Characters
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement
import Langlands.GroupScheme.Torus.FieldPointMaximality
import Langlands.GroupScheme.Torus.Relative
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Statement: central quotients of reductive group schemes and their maximal tori -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Central quotients of reductive group schemes** (Conrad, *Reductive group schemes*
(2014), Corollary 3.3.5 and Exercise 5.5.9(i)). Let `G` be a reductive group scheme over a
scheme `S`, let `z : Z ⟶ G` be a central closed subgroup with `Z` flat over `S`, and let
`q : G ⟶ G'` be an fppf quotient of `G` by the range of `z`. Then:
1. `G'` is reductive over `S`;
2. the centre of `G'` is `Z_G/Z`: its preimage under `q` is the centre of `G`;
3. for every maximal torus `T` of `G` there is a maximal torus `T'` of `G'` whose preimage
   under `q` is `T`, i.e. `T' = T/Z`;
4. every maximal torus `T'` of `G'` is `T/Z` for the maximal torus `T = q⁻¹(T')` of `G`;
5. a maximal torus of `G'` is determined by its preimage under `q`.
A maximal torus of a group `H` over `S` is a closed subgroup `t : T ⟶ H` with `T` an
`S`-torus whose residue fibres are maximal tori. -/
def RelativeCentralQuotientStatement : Prop :=
  ∀ (S : Scheme.{u}) (G : GroupScheme S), IsReductive G →
    ∀ (Z : GroupScheme S) (z : Z ⟶ G), IsClosedSubgroup z → IsCentral z → Flat Z.X.hom →
    ∀ (G' : GroupScheme S) (q : G ⟶ G'),
      RelativeRoot.IsFppfQuotient (SubgroupFunctor.range z) q →
      let IsMaxTorus : ∀ {H : GroupScheme S} {T : CommGroupScheme S}, (T.toGrp ⟶ H) → Prop :=
        fun {_} {T} t => RelativeTorus.IsTorus T.toGrp ∧ IsClosedSubgroup t ∧
          IsFibrewiseMaximalTorus t
      IsReductive G' ∧
      (center G').comap q = center G ∧
      (∀ (T : CommGroupScheme S) (t : T.toGrp ⟶ G), IsMaxTorus t →
        ∃ (T' : CommGroupScheme S) (t' : T'.toGrp ⟶ G'), IsMaxTorus t' ∧
          (SubgroupFunctor.range t').comap q = SubgroupFunctor.range t) ∧
      (∀ (T' : CommGroupScheme S) (t' : T'.toGrp ⟶ G'), IsMaxTorus t' →
        ∃ (T : CommGroupScheme S) (t : T.toGrp ⟶ G), IsMaxTorus t ∧
          (SubgroupFunctor.range t').comap q = SubgroupFunctor.range t) ∧
      (∀ (T₁ T₂ : CommGroupScheme S) (t₁ : T₁.toGrp ⟶ G') (t₂ : T₂.toGrp ⟶ G'),
        IsMaxTorus t₁ → IsMaxTorus t₂ →
        (SubgroupFunctor.range t₁).comap q = (SubgroupFunctor.range t₂).comap q →
        SubgroupFunctor.range t₁ = SubgroupFunctor.range t₂)

end Langlands.GroupScheme
