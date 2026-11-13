import Langlands.GroupScheme.RelativeLevi.Basic
import Langlands.GroupScheme.Reductive.QuasiSplit

/-! # Statement: the Borel locus of a parabolic subgroup scheme is open and closed -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **The Borel locus of a parabolic subgroup is open and closed** (Conrad, *Reductive group
schemes* (2014), Theorem 5.2.11(1)). For every scheme `S`, reductive group scheme `G` over `S`
and parabolic subgroup `i : P ⟶ G` in the sense of `IsRelativeParabolicSubgroup`, the set of
points `s` of `S` at which the residue-field fibre `i_s : P_s ⟶ G_s` is a Borel subgroup in
the sense of `IsGeometricBorelSubgroup` is open and closed in `S`. -/
def RelativeBorelLocusClopenStatement : Prop :=
  ∀ (S : Scheme.{u}) (G P : GroupScheme S) (i : P ⟶ G),
    IsReductive G → IsRelativeParabolicSubgroup i →
      IsClopen {s : S | IsGeometricBorelSubgroup (RelativeLevi.residueFiberHom i s)}

end Langlands.GroupScheme
