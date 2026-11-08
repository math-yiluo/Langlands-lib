import Langlands.GroupScheme.Reductive.AlmostSimple

/-! # Absolute almost-simplicity over a field -/

universe u

open AlgebraicGeometry

namespace Langlands.GroupScheme

/-- An almost-simple field group is absolutely almost-simple when it remains
almost-simple after the published base change to the algebraic closure. -/
def IsAbsolutelyAlmostSimple {k : Type u} [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) : Prop :=
  IsAlmostSimple G ∧
    IsAlmostSimple ((GroupScheme.baseChange (toAlgebraicClosure k)).obj G)

end Langlands.GroupScheme
