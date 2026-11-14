import Langlands.GroupScheme.Torus.RelativeMultiplicativeType
import Langlands.GroupScheme.Torus.Relative
import Langlands.GroupScheme.Reductive.Basic

/-! # Statement: the largest subtorus over an arbitrary base -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A group of multiplicative type has a largest closed subtorus, and every
largest closed subtorus remains largest after arbitrary base change
(Conrad, Remark B.1.2). -/
def RelativeMultiplicativeTypeLargestSubtorusStatement : Prop :=
  let IsLargestSubtorus :
      ∀ {S : Scheme.{u}} {H T : GroupScheme S}, (T ⟶ H) → Prop :=
    fun {S H T} t => IsClosedSubgroup t ∧ RelativeTorus.IsTorus T ∧
      ∀ (T' : GroupScheme S) (t' : T' ⟶ H),
        IsClosedSubgroup t' → RelativeTorus.IsTorus T' →
          ∃ f : T' ⟶ T, f ≫ t = t'
  ∀ (S : Scheme.{u}) (H : GroupScheme S),
    RelativeMultiplicativeType.IsMultiplicativeType H →
      (∃ (T : GroupScheme S) (t : T ⟶ H), IsLargestSubtorus t) ∧
      ∀ (T : GroupScheme S) (t : T ⟶ H), IsLargestSubtorus t →
        ∀ (S' : Scheme.{u}) (b : S' ⟶ S),
          IsLargestSubtorus ((GroupScheme.baseChange b).map t)

end Langlands.GroupScheme
