import Langlands.Global.AdelesLocallyCompactProof
import Langlands.Global.PrincipalAdelesDiscreteProof
import Langlands.Global.AdeleQuotientCompactProof

/-!
# Local compactness, discrete principal adeles, and compact additive quotient

The three published component proofs give `AdeleQuotientStatement`.
See `AdeleQuotientProof.md`.
-/

universe u

namespace Langlands.Global

/-- For every number field, the adeles are locally compact, the principal adeles
are discrete and closed, and the additive adele quotient is compact. -/
theorem adeleQuotient : AdeleQuotientStatement.{u} := by
  intro K _ _
  exact ⟨adelesLocallyCompact K, principalAdelesDiscrete K, adeleQuotientCompact K⟩

end Langlands.Global
