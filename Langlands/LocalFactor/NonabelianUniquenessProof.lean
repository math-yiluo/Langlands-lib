import Langlands.LocalFactor.CommonClosureGenerationProof

/-!
# Uniqueness of common-closure local-constant systems

The proved degree-zero generation theorem discharges the premise of the
published uniqueness reduction, for independent field and carrier universes.
-/

noncomputable section

universe uF uV

namespace Langlands.LocalFactor

namespace NonabelianSystem

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- Two local-constant systems for the same supplied reciprocity family agree
on every actual common-closure input. -/
theorem unique (e : CommonClosure.ReciprocityFamily F) :
    Unique.{uF, uV} F e :=
  unique_of_commonClosureDegreeZeroGeneration F
    (commonClosureDegreeZeroGeneration.{uF, uV} p F) e

end NonabelianSystem

/-- Same-family uniqueness over every finite p-adic field, with independent
field and representation-carrier universes. -/
theorem nonabelianSystemUniqueness :
    NonabelianSystemUniquenessStatement.{uF, uV} := by
  intro p hp F e
  exact NonabelianSystem.unique F e

end Langlands.LocalFactor
