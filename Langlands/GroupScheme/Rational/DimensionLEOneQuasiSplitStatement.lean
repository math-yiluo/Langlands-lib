import Langlands.FieldTheory.DimensionLEOne
import Langlands.GroupScheme.Reductive.QuasiSplit

/-! # Steinberg's quasi-splitness statement for fields of dimension at most one -/

universe u

open AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Connected reductive groups over fields satisfying the finite-separable
norm criterion for dimension at most one have field-defined geometric Borels. -/
def DimensionLEOneQuasiSplitStatement : Prop :=
  ∀ (K : Type u) [Field K],
    Langlands.FieldTheory.HasDimensionLEOne K →
    ∀ (H : GroupScheme (Spec (CommRingCat.of K))),
      IsConnectedReductive H → IsQuasiSplit H

end Langlands.GroupScheme
