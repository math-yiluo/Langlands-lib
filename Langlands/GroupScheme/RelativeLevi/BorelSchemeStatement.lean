import Langlands.GroupScheme.RelativeLevi.Borel
import Langlands.GroupScheme.HomScheme.TorusSubgroupModuli
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-! # Statement: the scheme of Borel subgroups of a reductive group scheme -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **The scheme of Borel subgroups** (Conrad, *Reductive group schemes* (2014),
Theorem 5.2.11(3)). For every scheme `S` and every reductive group scheme `G` over `S` there
is an `S`-scheme `M` with a Borel subgroup `j : B ⟶ G_M` (the universal Borel subgroup) such
that for every `S`-scheme `T` and every Borel subgroup `i` of `G_T`, exactly one `S`-morphism
`a : T ⟶ M` pulls `j` back to a subgroup of `G_T` with the same image as `i`. Moreover
`M ⟶ S` is smooth and proper. -/
def RelativeBorelSchemeStatement : Prop :=
  ∀ (S : Scheme.{u}) (G : GroupScheme S), IsReductive G →
    ∃ (M : Over S) (B : GroupScheme M.left) (j : B ⟶ (GroupScheme.baseChange M.hom).obj G),
      IsRelativeBorelSubgroup j ∧
      (∀ (T : Over S) (B' : GroupScheme T.left) (i : B' ⟶ (GroupScheme.baseChange T.hom).obj G),
        IsRelativeBorelSubgroup i →
          ∃! a : T ⟶ M, TorusSubgroupModuli.evaluate j a = SubgroupFunctor.range i) ∧
      Smooth M.hom ∧ IsProper M.hom

end Langlands.GroupScheme
