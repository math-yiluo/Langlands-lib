import Langlands.GroupScheme.Symplectic.Basic
import Langlands.GroupScheme.Reductive.AbsolutelyAlmostSimple

/-! # Simple connectedness and absolute almost-simplicity of the standard Sp group -/

universe u

namespace Langlands.GroupScheme.Symplectic

/-- Over every field, the standard symplectic group of positive rank at least two
is simply connected and absolutely almost-simple, including in characteristic two. -/
def StructureStatement : Prop :=
  ∀ (K : Type u) [Field K] (n : ℕ), 2 ≤ n →
    IsSimplyConnected (groupScheme K n) ∧ IsAbsolutelyAlmostSimple (groupScheme K n)

end Langlands.GroupScheme.Symplectic
