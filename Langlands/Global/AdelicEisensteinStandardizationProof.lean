import Langlands.Global.AdelicEisensteinStandardizationReduction
import Langlands.Geometry.Building.BruhatTitsAvailabilityReductionProof
import Langlands.Geometry.Building.GroupAxiomsExistenceProof

/-! # Passage of Eisenstein series to a standard family with a compact in good position -/

universe u

namespace Langlands.Global

/-- An Eisenstein series for an arbitrary parabolic with a root presentation and an arbitrary
maximal compact Iwasawa subgroup is, after an archimedean right translation, a finite
combination with entire exponential coefficients of Eisenstein series for the corresponding
standard parabolic of a standard family and a maximal compact subgroup in good position. -/
theorem eisensteinStandardization : EisensteinStandardizationStatement.{u} :=
  eisensteinStandardization_of_bruhatTitsAvailability
    (Geometry.Building.bruhatTitsAvailabilityReduction Geometry.Building.groupAxiomsExistence)

end Langlands.Global
