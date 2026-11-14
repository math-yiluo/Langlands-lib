import Langlands.GroupScheme.Dynamic.Functoriality
import Langlands.GroupScheme.Rational.Characters
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement
import Langlands.GroupScheme.RelativeLevi.Borel

/-! # Statement: parabolic subgroups of a reductive group and of its adjoint quotient -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Parabolic subgroups of `G` and of `G^ad`** (Conrad, *Reductive group schemes* (2014),
Exercise 5.5.8). Let `G` be a reductive group scheme over a scheme `S`. Then every parabolic
subgroup of `G` contains the centre `Z_G`, and for every fppf quotient `q : G ⟶ G^ad` of `G` by
its centre, `P ↦ P/Z_G` is a bijection between the parabolic subgroups of `G` and those of
`G^ad`, with inverse `P' ↦ q⁻¹(P')`: every parabolic `P` of `G` is `q⁻¹(P')` for a parabolic
`P'` of `G^ad`, every parabolic `P'` of `G^ad` has `q⁻¹(P')` parabolic in `G`, a parabolic
subgroup of `G^ad` is determined by its preimage, and the correspondence matches Borel
subgroups with Borel subgroups. -/
def AdjointParabolicCorrespondenceStatement : Prop :=
  ∀ (S : Scheme.{u}) (G : GroupScheme S), IsReductive G →
    (∀ (P : GroupScheme S) (i : P ⟶ G), IsRelativeParabolicSubgroup i →
      center G ≤ SubgroupFunctor.range i) ∧
    ∀ (Gad : GroupScheme S) (q : G ⟶ Gad), RelativeRoot.IsFppfQuotient (center G) q →
      (∀ (P : GroupScheme S) (i : P ⟶ G), IsRelativeParabolicSubgroup i →
        ∃ (P' : GroupScheme S) (i' : P' ⟶ Gad), IsRelativeParabolicSubgroup i' ∧
          (SubgroupFunctor.range i').comap q = SubgroupFunctor.range i) ∧
      (∀ (P' : GroupScheme S) (i' : P' ⟶ Gad), IsRelativeParabolicSubgroup i' →
        ∃ (P : GroupScheme S) (i : P ⟶ G), IsRelativeParabolicSubgroup i ∧
          (SubgroupFunctor.range i').comap q = SubgroupFunctor.range i) ∧
      (∀ (P₁ P₂ : GroupScheme S) (i₁ : P₁ ⟶ Gad) (i₂ : P₂ ⟶ Gad),
        IsRelativeParabolicSubgroup i₁ → IsRelativeParabolicSubgroup i₂ →
        (SubgroupFunctor.range i₁).comap q = (SubgroupFunctor.range i₂).comap q →
        SubgroupFunctor.range i₁ = SubgroupFunctor.range i₂) ∧
      (∀ (P : GroupScheme S) (i : P ⟶ G) (P' : GroupScheme S) (i' : P' ⟶ Gad),
        IsRelativeParabolicSubgroup i → IsRelativeParabolicSubgroup i' →
        (SubgroupFunctor.range i').comap q = SubgroupFunctor.range i →
        (IsRelativeBorelSubgroup i ↔ IsRelativeBorelSubgroup i'))

end Langlands.GroupScheme
