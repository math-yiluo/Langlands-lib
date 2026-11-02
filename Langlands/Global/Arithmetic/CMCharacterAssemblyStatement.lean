import Langlands.Global.Arithmetic.CMCharacterStatement

/-!
# Reduction of regular CM unit prescription to its three inputs

The target keeps the existence of each arithmetic input explicit and asserts
only the assembly implication on the existing Hecke-character objects.
-/

universe u v

namespace Langlands.Global

/-- Unramified infinity realization, finite self-dual prescription, and local
integral-unit extension suffice for regular CM unit prescription. -/
def CMRegularUnitPrescriptionOfInputsStatement : Prop :=
  CMUnramifiedInfinityRealizationStatement.{u} →
  CMFiniteCharacterPrescriptionStatement.{u} →
  IntegralUnitCharacterExtensionStatement.{u} →
  CMRegularUnitPrescriptionStatement.{u,v}

end Langlands.Global
