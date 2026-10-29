import Langlands.Algebra.RenardEndomorphismQuotient

/-! # Injectivity on the power-kernel quotient and its localization comparison -/

set_option autoImplicit false

universe u v

namespace Langlands.Renard.EndomorphismLocalization

/-- The induced endomorphism `a'` of `V / K` is injective. -/
def QuotientEndInjectiveStatement : Prop :=
  ∀ (R : Type u) [CommRing R] (V : Type v) [AddCommGroup V] [Module R V]
    (a : Module.End R V),
    Function.Injective (quotientEnd a)

/-- The canonical map `ι'` of `V / K` into its localization at `a'` is injective. -/
def QuotientIotaInjectiveStatement : Prop :=
  ∀ (R : Type u) [CommRing R] (V : Type v) [AddCommGroup V] [Module R V]
    (a : Module.End R V),
    Function.Injective (iota (quotientEnd a))

/-- There is a unique equivalence from the localization of `V / K` at `a'` to the
localization of `V` at `a` that intertwines the localized operators and carries
`ι' ∘ π` to `ι`. -/
def QuotientLocalizationComparisonStatement : Prop :=
  ∀ (R : Type u) [CommRing R] (V : Type v) [AddCommGroup V] [Module R V]
    (a : Module.End R V),
    ∃! e : Localized (quotientEnd a) ≃ₗ[R] Localized a,
      e.toLinearMap.comp ((iota (quotientEnd a)).comp (quotientProjection a)) = iota a ∧
        ∀ z : Localized (quotientEnd a),
          e (localizedEnd (quotientEnd a) z) = localizedEnd a (e z)

/-- The three ring statements together. -/
def QuotientLocalizationStatement : Prop :=
  QuotientEndInjectiveStatement.{u, v} ∧
    QuotientIotaInjectiveStatement.{u, v} ∧
    QuotientLocalizationComparisonStatement.{u, v}

/-- The source's field case of the same three conclusions. -/
def FieldQuotientLocalizationStatement : Prop :=
  ∀ (k : Type u) [Field k] (V : Type v) [AddCommGroup V] [Module k V]
    (a : Module.End k V),
    Function.Injective (quotientEnd a) ∧
      Function.Injective (iota (quotientEnd a)) ∧
      ∃! e : Localized (quotientEnd a) ≃ₗ[k] Localized a,
        e.toLinearMap.comp ((iota (quotientEnd a)).comp (quotientProjection a)) = iota a ∧
          ∀ z : Localized (quotientEnd a),
            e (localizedEnd (quotientEnd a) z) = localizedEnd a (e z)

/-- Closed aggregate: the ring statements and their field specialization. -/
def QuotientLocalizationStatements : Prop :=
  QuotientLocalizationStatement.{u, v} ∧ FieldQuotientLocalizationStatement.{u, v}

end Langlands.Renard.EndomorphismLocalization
