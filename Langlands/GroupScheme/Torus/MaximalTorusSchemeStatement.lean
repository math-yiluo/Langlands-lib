import Langlands.GroupScheme.Torus.FieldPointMaximality
import Langlands.GroupScheme.HomScheme.TorusSubgroupModuli
import Mathlib.AlgebraicGeometry.QuasiAffine

/-! # Statement: the scheme of maximal tori of a reductive group scheme -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **The scheme of maximal tori** (Conrad, *Reductive group schemes* (2014), Theorem 3.2.6,
first assertion, for reductive group schemes). For every scheme `S` and every reductive group
scheme `G` over `S` there is an `S`-scheme `M` with a closed relative torus `j : K ⟶ G_M`
that is a maximal torus on every residue-field fibre of `M`, such that for every `S`-scheme
`T` and every closed relative torus of `G_T` that is a maximal torus on every residue-field
fibre of `T`, exactly one `S`-morphism `a : T ⟶ M` pulls `j` back to a subgroup with the same
image. Moreover `M ⟶ S` is smooth and surjective, and the preimage of every affine open of
`S` is a quasi-affine scheme. -/
def MaximalTorusSchemeStatement : Prop :=
  ∀ (S : Scheme.{u}) (G : GroupScheme S), IsReductive G →
    ∃ (M : Over S) (K : CommGroupScheme M.left)
      (j : K.toGrp ⟶ (GroupScheme.baseChange M.hom).obj G),
      RelativeTorus.IsTorus K.toGrp ∧ IsClosedSubgroup j ∧ IsFibrewiseMaximalTorus j ∧
      (∀ (T : Over S) (T' : CommGroupScheme T.left)
          (t : T'.toGrp ⟶ (GroupScheme.baseChange T.hom).obj G),
        RelativeTorus.IsTorus T'.toGrp → IsClosedSubgroup t → IsFibrewiseMaximalTorus t →
          ∃! a : T ⟶ M, TorusSubgroupModuli.evaluate j a = SubgroupFunctor.range t) ∧
      Smooth M.hom ∧ Surjective M.hom ∧
      ∀ V : S.affineOpens, (M.hom ⁻¹ᵁ (V : S.Opens)).toScheme.IsQuasiAffine

end Langlands.GroupScheme
