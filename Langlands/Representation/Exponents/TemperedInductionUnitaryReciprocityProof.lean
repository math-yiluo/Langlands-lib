import Langlands.Representation.Exponents.TemperedInductionUnitaryReciprocityReduction
import Langlands.Representation.Exponents.LeviFrobeniusReciprocityProof
import Langlands.Representation.Exponents.TemperedJacquetUnitaryRestrictionProof

/-! # Tempered Frobenius reciprocity through the unitary Jacquet part

Renard 2026, VII.2.4, Proposition (printed p.229/PDF p.235). The proof composes Frobenius
reciprocity with restriction to the unitary Jacquet part, through the published
conditional assembly `temperedInductionUnitaryReciprocity_of`.
-/

universe u v w

namespace Langlands.Aubert.General.RepresentedParabolic

/-- Renard VII.2.4, Proposition: for tempered `π` of `G(F)` and tempered `σ` of `M(F)`,
evaluation at the identity restricted to the unitary Jacquet part gives a linear bijection
`Hom_G(π, i_P^G σ) ≃ Hom_M((r_P^G π)_0, σ)`. -/
theorem temperedInductionUnitaryReciprocity :
    TemperedInductionUnitaryReciprocityStatement.{u, v, w} :=
  temperedInductionUnitaryReciprocity_of leviFrobeniusReciprocity.{u, v, w}
    temperedJacquetUnitaryRestriction.{u, max v w}

end Langlands.Aubert.General.RepresentedParabolic
