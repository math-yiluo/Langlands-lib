import Langlands.Algebra.RenardEndomorphismLocalization
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Actual localization, stable powers, and the canonical stable image

Internal ordinary-unital-module statements motivated by Renard 2026,
Appendix C.II, printed page 279 / PDF page 285. The full possibly nonunital
complex-algebra proposition remains a separate obligation.
-/

universe uR uV

namespace Langlands.Renard.EndomorphismLocalization

/-- The actual localization is canonically the stable image, compatibly with
the localized endomorphism. Both equations belong to the uniqueness predicate. -/
def StablePowerImageAt {R : Type uR} [CommRing R] {V : Type uV}
    [AddCommGroup V] [Module R V] (a : Module.End R V) (n : ℕ) : Prop :=
  IsCompl (LinearMap.ker (a ^ n)) (LinearMap.range (a ^ n)) ∧
    ∃! e : Localized a ≃ₗ[R] LinearMap.range (a ^ n),
      (LinearMap.range (a ^ n)).subtype.comp (e.toLinearMap.comp (localizedEnd a)) =
          a.comp ((LinearMap.range (a ^ n)).subtype.comp e.toLinearMap) ∧
        e.symm.toLinearMap = (iota a).comp (LinearMap.range (a ^ n)).subtype

/-- Noetherianity of the actual source and localization gives surjectivity
and one common positive exponent for the canonical kernel and both stability
equalities. Ring Noetherianity and finite generation are not premises. -/
def NoetherianActualLocalizationStatement : Prop :=
  ∀ (R : Type uR) [CommRing R] (V : Type uV) [AddCommGroup V] [Module R V]
      (a : Module.End R V),
    IsNoetherian R V → IsNoetherian R (Localized a) →
      Function.Surjective (iota a) ∧
        ∃ n : ℕ, 0 < n ∧
          LinearMap.ker (iota a) = LinearMap.ker (a ^ n) ∧
          LinearMap.ker (a ^ n) = LinearMap.ker ((a ^ n) ^ 2) ∧
          LinearMap.range (a ^ n) = LinearMap.range ((a ^ n) ^ 2)

/-- Every positive stable power gives the canonical stable-image
identification, with no Noetherian or finite-generation hypothesis. -/
def StablePowerImageStatement : Prop :=
  ∀ (R : Type uR) [CommRing R] (V : Type uV) [AddCommGroup V] [Module R V]
      (a : Module.End R V) (n : ℕ),
    0 < n →
      LinearMap.ker (a ^ n) = LinearMap.ker ((a ^ n) ^ 2) →
      LinearMap.range (a ^ n) = LinearMap.range ((a ^ n) ^ 2) →
      StablePowerImageAt a n

/-- Finite source and actual localization modules over a Noetherian
commutative ring give a common positive stable exponent and the canonical
identification for every positive stable exponent. -/
def FiniteActualLocalizationStatement : Prop :=
  ∀ (R : Type uR) [CommRing R] (V : Type uV) [AddCommGroup V] [Module R V]
      (a : Module.End R V),
    IsNoetherianRing R → Module.Finite R V → Module.Finite R (Localized a) →
      Function.Surjective (iota a) ∧
        (∃ n : ℕ, 0 < n ∧
          LinearMap.ker (iota a) = LinearMap.ker (a ^ n) ∧
          LinearMap.ker (a ^ n) = LinearMap.ker ((a ^ n) ^ 2) ∧
          LinearMap.range (a ^ n) = LinearMap.range ((a ^ n) ^ 2)) ∧
        ∀ n : ℕ, 0 < n →
          LinearMap.ker (a ^ n) = LinearMap.ker ((a ^ n) ^ 2) →
          LinearMap.range (a ^ n) = LinearMap.range ((a ^ n) ^ 2) →
          StablePowerImageAt a n

/-- The complete internal ordinary-module actual-localization stability
statement family, at independent coefficient and carrier universes. -/
def ActualLocalizationStabilityStatements : Prop :=
  NoetherianActualLocalizationStatement.{uR, uV} ∧
    StablePowerImageStatement.{uR, uV} ∧
    FiniteActualLocalizationStatement.{uR, uV}

end Langlands.Renard.EndomorphismLocalization
