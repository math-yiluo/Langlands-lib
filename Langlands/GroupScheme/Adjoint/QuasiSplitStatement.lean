import Langlands.GroupScheme.Adjoint.Quotient
import Langlands.GroupScheme.Reductive.QuasiSplit

/-! # Quasi-splitness of a supplied adjoint quotient -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A supplied actual full-centre adjoint quotient preserves quasi-splitness. -/
def AdjointQuotientQuasiSplitStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G A : GroupScheme (Spec (CommRingCat.of k))) (q : G ⟶ A),
    IsAdjointQuotient q → IsQuasiSplit G → IsQuasiSplit A

end Langlands.GroupScheme
