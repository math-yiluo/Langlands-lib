import Langlands.AbelianScheme.GroupScheme
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Group schemes over a field are separated -/

universe u

open AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Every group scheme over the spectrum of an arbitrary field has separated structure
morphism. -/
def FieldSeparatedStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G : Langlands.GroupScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k)))),
    IsSeparated G.X.hom

end Langlands.GroupScheme
