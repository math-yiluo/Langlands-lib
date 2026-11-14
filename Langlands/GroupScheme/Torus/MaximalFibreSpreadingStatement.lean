import Langlands.GroupScheme.Torus.FieldPointMaximality
import Langlands.GroupScheme.Torus.Relative
import Langlands.GroupScheme.Rational.TorusCentralizer
import Langlands.GroupScheme.Reductive.IdentityComponentLocus
import Langlands.GroupScheme.RelativeIdentityComponent

/-! # Statement: maximality of a torus in a reductive fibre spreads to a neighbourhood -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Maximality of a torus spreads out** (Conrad, *Reductive group schemes* (2014),
Proposition 3.1.9(2); compare SGA 3, XIX, 2.6). Let `G → S` be a smooth `S`-affine group
scheme, `i : T ⟶ G` a closed subgroup that is a torus over `S`, and `s ∈ S` a point at
which the identity component of the geometric fibre is reductive and the residue fibre
`T_s ⟶ G_s` is a maximal torus. Then there is an open neighbourhood `V` of `s` such that
`T_v ⟶ G_v` is a maximal torus for every `v ∈ V`, and `T_V` is the relative identity
component of `Z_G(T)_V` for every subgroup `Z ⟶ G` representing the centralizer of `T`. -/
def MaximalTorusFibreSpreadingStatement : Prop :=
  ∀ (S : Scheme.{u}) (G : GroupScheme S) [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (T : CommGroupScheme S) (i : T.toGrp ⟶ G),
    RelativeTorus.IsTorus T.toGrp → IsClosedSubgroup i →
    ∀ s : S, s ∈ identityComponentReductiveLocus G →
      IsMaximalTorus (T := (CommGroupScheme.baseChange (S.fromSpecResidueField s)).obj T)
        ((GroupScheme.baseChange (S.fromSpecResidueField s)).map i) →
      ∃ V : S.Opens, s ∈ V ∧
        (∀ v : S, v ∈ V →
          IsMaximalTorus (T := (CommGroupScheme.baseChange (S.fromSpecResidueField v)).obj T)
            ((GroupScheme.baseChange (S.fromSpecResidueField v)).map i)) ∧
        ∀ (Z : GroupScheme S) (z : Z ⟶ G) (j : T.toGrp ⟶ Z),
          (torusCentralizer i).IsRepresentedBy z → j ≫ z = i →
          IsRelativeIdentityComponent ((GroupScheme.baseChange V.ι).obj Z)
            ((GroupScheme.baseChange V.ι).map j)

end Langlands.GroupScheme
