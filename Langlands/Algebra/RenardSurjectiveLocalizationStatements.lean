import Langlands.Algebra.RenardEndomorphismQuotient

/-!
# Surjective canonical map and the actual power-kernel quotient

Statement declarations for Renard A.III.1, the unnumbered corollary after
example 5, printed p. 253 / PDF p. 259, French edition of 9 July 2026.
The actual quotient and localization are imported from the published Library.
-/

set_option autoImplicit false

universe u v

namespace Langlands.Renard.EndomorphismLocalization

/-- Surjectivity of the actual localization map gives a unique compatible
equivalence from the actual localization to the actual power-kernel quotient. -/
def SurjectiveIotaQuotientStatement : Prop :=
  ∀ (R : Type u) [CommRing R] (V : Type v) [AddCommGroup V] [Module R V]
    (a : Module.End R V),
      Function.Surjective (iota a) →
        ∃! e : Localized a ≃ₗ[R] PowerKernelQuotient a,
          e.toLinearMap.comp (localizedEnd a) =
              (quotientEnd a).comp e.toLinearMap ∧
            e.toLinearMap.comp (iota a) = quotientProjection a

/-- The source-facing corollary over an arbitrary field and vector space. -/
def FieldSurjectiveIotaQuotientStatement : Prop :=
  ∀ (k : Type u) [Field k] (V : Type v) [AddCommGroup V] [Module k V]
    (a : Module.End k V),
      Function.Surjective (iota a) →
        ∃! e : Localized a ≃ₗ[k] PowerKernelQuotient a,
          e.toLinearMap.comp (localizedEnd a) =
              (quotientEnd a).comp e.toLinearMap ∧
            e.toLinearMap.comp (iota a) = quotientProjection a

/-- Ring-general corollary together with its explicit field specialization. -/
def SurjectiveIotaQuotientStatements : Prop :=
  SurjectiveIotaQuotientStatement.{u, v} ∧
    FieldSurjectiveIotaQuotientStatement.{u, v}

end Langlands.Renard.EndomorphismLocalization
