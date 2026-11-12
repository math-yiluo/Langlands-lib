import Langlands.AlgebraicGeometry.LangWeil.FiniteNormalizationCoverProof
import Langlands.AlgebraicGeometry.LangWeil.NormalizationCoverPointBound

/-!
# Uniform upper bounds for point counts in families over the integers

The finite normalization cover theorem supplies the geometric input to the
uniform counting reduction.
-/

universe u

namespace Langlands.AlgebraicGeometry.LangWeil

/-- The uniform upper bound for finite-field points in families over the integers. -/
theorem familyPointUpperBound : FamilyPointUpperBoundStatement.{u} :=
  familyPointUpperBound_of_finiteNormalizationCover finiteNormalizationCover

end Langlands.AlgebraicGeometry.LangWeil
