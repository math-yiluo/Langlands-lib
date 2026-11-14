import Langlands.GroupScheme.RelativeLevi.OppositeBorelStatement
import Langlands.GroupScheme.Dynamic.OppositeIntersection

/-! # Étale-local dynamic presentation of a Borel pair -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A Borel subgroup containing a maximal torus has, étale-locally on the
base, a dynamic presentation by a cocharacter of that torus. The cocharacter
has centralizer the given torus, and its negative dynamic parabolic is
represented by a relative Borel subgroup. This is the local construction
used in Conrad, *Reductive group schemes* (2014), Proposition 5.2.12,
from Proposition 5.2.3. -/
def RelativeBorelDynamicPresentationStatement : Prop :=
  ∀ (S : Scheme.{u}) (G B : GroupScheme S) (i : B ⟶ G)
    (T : CommGroupScheme S) (t : T.toGrp ⟶ G),
    IsReductive G →
    RelativeTorus.IsTorus T.toGrp → IsClosedSubgroup t → IsFibrewiseMaximalTorus t →
    IsRelativeBorelSubgroup i → SubgroupFunctor.range t ≤ SubgroupFunctor.range i →
      ∃ 𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S,
        ∀ a : 𝒰.I₀,
          let G' := (GroupScheme.baseChange (𝒰.f a)).obj G
          let T' := (CommGroupScheme.baseChange (𝒰.f a)).obj T
          let i' := (GroupScheme.baseChange (𝒰.f a)).map i
          let t' := (GroupScheme.baseChange (𝒰.f a)).map t
          IsSplitTorus T'.toGrp ∧
            ∃ ν : cocharacterLattice T',
              let χ := CommGroupScheme.groupHom ν ≫ t'
              SubgroupFunctor.range i' = Dynamic.parabolic χ ∧
                Dynamic.centralizer χ = SubgroupFunctor.range t' ∧
                ∃ (Bminus : GroupScheme (𝒰.X a)) (iminus : Bminus ⟶ G'),
                  IsRelativeBorelSubgroup iminus ∧
                    SubgroupFunctor.range iminus =
                      Dynamic.parabolic (Dynamic.oppositeCocharacter χ)

end Langlands.GroupScheme
