import Langlands.GroupScheme.Rational.QuasiSplitInnerForm

/-! # Quasi-split inner forms of connected reductive field groups -/

universe u

open AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Every connected reductive field group is an actual finite-Galois inner twist
of a quasi-split field group, with an adjoint-valued discrepancy cocycle. -/
def QuasiSplitInnerFormExistenceStatement : Prop :=
  ∀ (K : Type u) [Field K]
    (G : GroupScheme (Spec (CommRingCat.of K))),
    IsConnectedReductive G → Nonempty (QuasiSplitInnerForm G)

end Langlands.GroupScheme
