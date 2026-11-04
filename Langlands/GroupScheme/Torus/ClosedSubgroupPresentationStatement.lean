import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.Torus.Diagonalizable
import Mathlib.GroupTheory.Finiteness

/-! # Statement: closed subgroups of diagonalizable groups are diagonalizable -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.Diagonalizable

/-- Milne (2022), Theorems 12.8 and 12.9(a),(c): over a field `k`, every closed subgroup
`i : H ⟶ D(Λ)` of the diagonalizable group of a finitely generated abelian group `Λ` is
isomorphic, as a group scheme over `k`, to `D(Λ')` for some finitely generated abelian group
`Λ'`. The subgroup need not be smooth, connected or reduced, and `Λ'` may have torsion. -/
def ClosedSubgroupPresentationStatement : Prop :=
  ∀ (k : Type u) [Field k] (Λ : Type u) [AddCommGroup Λ] [AddGroup.FG Λ]
    (H : GroupScheme (Spec (CommRingCat.of k)))
    (i : H ⟶ (groupScheme (CommRingCat.of k) Λ).toGrp),
    IsClosedSubgroup i →
      ∃ (Λ' : Type u) (_ : AddCommGroup Λ') (_ : AddGroup.FG Λ'),
        Nonempty (H ≅ (groupScheme (CommRingCat.of k) Λ').toGrp)

end Langlands.GroupScheme.Diagonalizable
