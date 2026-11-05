import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.Rational.InvariantCoordinateIntegral

/-! # Invariant integration for reductive groups in characteristic zero -/

universe u

open AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Every connected reductive affine group over a characteristic-zero field
admits normalized invariant integration on its actual coordinate algebra. -/
def CharacteristicZeroReductiveInvariantIntegralStatement : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k]
    (H : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom H.X.hom],
    IsConnectedReductive H → Nonempty (CoordinateIntegration.InvariantIntegral H)

end Langlands.GroupScheme
