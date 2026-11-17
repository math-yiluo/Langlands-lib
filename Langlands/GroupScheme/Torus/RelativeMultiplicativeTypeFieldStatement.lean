import Langlands.GroupScheme.Torus.RelativeMultiplicativeType
import Langlands.GroupScheme.Torus.MultiplicativeType

/-! # Statement: field-valued fibres of relative multiplicative-type groups -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Relative multiplicative type implies field-level multiplicative type after
every field-valued base change. -/
def RelativeMultiplicativeTypeFieldStatement : Prop :=
  ∀ (S : Scheme.{u}) (G : GroupScheme S),
    RelativeMultiplicativeType.IsMultiplicativeType G →
      ∀ (k : Type u) [Field k] (b : Spec (CommRingCat.of k) ⟶ S),
        IsMultiplicativeType ((GroupScheme.baseChange b).obj G)

end Langlands.GroupScheme
