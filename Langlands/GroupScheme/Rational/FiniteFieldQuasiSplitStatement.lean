import Langlands.GroupScheme.Reductive.QuasiSplit

/-! # Statement: connected reductive groups over finite fields are quasi-split -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Every connected reductive group over a finite field contains a ground-field Borel
subgroup whose algebraic-closure base change is also Borel. -/
def FiniteFieldQuasiSplitStatement : Prop :=
  ∀ (k : Type u) [Field k] [Finite k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G → IsQuasiSplit G

end Langlands.GroupScheme
