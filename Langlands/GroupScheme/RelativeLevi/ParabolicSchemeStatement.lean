import Langlands.GroupScheme.RelativeLevi.Basic
import Langlands.GroupScheme.HomScheme.TorusSubgroupModuli
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Statement: the scheme of parabolic subgroups of a reductive group scheme -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **The scheme of parabolic subgroups** (Conrad, *Reductive group schemes* (2014),
Corollary 5.2.9). For every scheme `S` and every reductive group scheme `G` over `S` there is
an `S`-scheme `M` with a parabolic subgroup `j : P ⟶ G_M` (the universal parabolic subgroup)
such that for every `S`-scheme `T` and every parabolic subgroup `i` of `G_T`, exactly one
`S`-morphism `a : T ⟶ M` pulls `j` back to a subgroup of `G_T` with the same image as `i`.
Moreover `M ⟶ S` is smooth and proper. -/
def RelativeParabolicSchemeStatement : Prop :=
  ∀ (S : Scheme.{u}) (G : GroupScheme S), IsReductive G →
    ∃ (M : Over S) (P : GroupScheme M.left) (j : P ⟶ (GroupScheme.baseChange M.hom).obj G),
      IsRelativeParabolicSubgroup j ∧
      (∀ (T : Over S) (Q : GroupScheme T.left) (i : Q ⟶ (GroupScheme.baseChange T.hom).obj G),
        IsRelativeParabolicSubgroup i →
          ∃! a : T ⟶ M, TorusSubgroupModuli.evaluate j a = SubgroupFunctor.range i) ∧
      Smooth M.hom ∧ IsProper M.hom

end Langlands.GroupScheme
