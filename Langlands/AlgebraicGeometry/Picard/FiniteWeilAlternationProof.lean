import Langlands.AlgebraicGeometry.Picard.FiniteWeilAlternationReduction
import Langlands.AbelianScheme.MultiplicationIsogenyProof

/-! # Alternation of the actual finite pairing of a relative polarization -/

universe u

namespace Langlands.AbelianScheme

/-- The actual finite pairing of every relative polarization is trivial on the
diagonal, with all the hypotheses of the published target unchanged. -/
theorem relativeFiniteWeilAlternation : RelativeFiniteWeilAlternationStatement.{u} :=
  relativeFiniteWeilAlternation_of_multiplicationIsogeny
    Langlands.GroupScheme.multiplicationIsogeny

end Langlands.AbelianScheme
