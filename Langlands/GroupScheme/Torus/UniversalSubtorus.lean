import Langlands.GroupScheme.Torus.Relative
import Langlands.GroupScheme.SubgroupBaseChange
import Langlands.GroupScheme.Rational.LeviFactorization

/-! # A universal property for the largest subtorus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A closed relative torus through which every homomorphism from a relative
torus factors, even after arbitrary base change. -/
def IsUniversalSubtorus {S : Scheme.{u}} {H T : GroupScheme S} (j : T ⟶ H) : Prop :=
  IsClosedSubgroup j ∧ RelativeTorus.IsTorus T ∧
    ∀ (S' : Scheme.{u}) (b : S' ⟶ S) (T' : GroupScheme S')
      (f : T' ⟶ (GroupScheme.baseChange b).obj H),
      RelativeTorus.IsTorus T' →
        ∃ a : T' ⟶ (GroupScheme.baseChange b).obj T,
          a ≫ (GroupScheme.baseChange b).map j = f

end Langlands.GroupScheme
