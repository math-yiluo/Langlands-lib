import Langlands.Representation.Parabolic.NaturalInductionDualityFromScalar
import Langlands.Representation.Induction.CompactScalarProof

/-!
# Natural normalized induction duality

The compact-picture pairing gives natural equivalences between the smooth dual
of a normalized induced representation and the normalized induction of the
smooth dual, for standard GL parabolics and for refined parabolics of product
Levis.
-/

namespace Langlands.Parabolic

universe uF uV

/-- Natural normalized induction duality, standard and refined. -/
theorem naturalNormalizedInductionDuality :
    NaturalNormalizedInductionDualityStatement.{uF, uV} :=
  naturalNormalizedInductionDuality_of_scalar glParabolicCompactScalarIntegral.{uF}

end Langlands.Parabolic
