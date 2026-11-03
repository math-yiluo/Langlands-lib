import Langlands.GroupScheme.CorepresentedClosedSubgroup
import Langlands.GroupScheme.Reductive.Basic

/-! # Unipotence of the upper unitriangular group scheme over a field -/

universe u

namespace Langlands.GroupScheme

/-- The concrete upper unitriangular group scheme is unipotent over every field, in every
dimension including zero. This is a proposition target corresponding to Milne 2017,
Theorem 14.5(b)⇒(a), not a proof. -/
def UnitriangularUnipotentStatement : Prop :=
  ∀ (k : Type u) [Field k] (N : ℕ),
    IsUnipotent (GeneralLinear.blockUnipotentScheme (Fin N) (CommRingCat.of k)
      (fun i => -(i.val : ℤ)))

end Langlands.GroupScheme
