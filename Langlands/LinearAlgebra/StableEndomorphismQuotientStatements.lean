import Langlands.LinearAlgebra.StableEndomorphismQuotients

/-!
# Exactness assertions for successive kernel and range quotients

Prop-valued targets for Renard 2026, Appendix C.II, proof of Lemma (iv),
printed page 278 / PDF page 284. The arbitrary-ring version is an internal
strengthening of the source's complex-vector-space assertions.
-/

set_option autoImplicit false

universe uR uV

namespace Langlands.LinearAlgebra.StableEndomorphism

/-- The prequotient kernel, all arrow kernel/image formulas, endpoint
injectivity/surjectivity, and exactness of the actual successive quotient maps. -/
def PowerQuotientExactnessAt
    {R : Type uR} [Ring R] {V : Type uV} [AddCommGroup V] [Module R V]
    (t : Module.End R V) (k : ℕ) : Prop :=
  LinearMap.ker (kerShiftMk t k) = kerPowInSucc t (k + 1) ∧
    LinearMap.ker (kerToRangeQuotient t k) =
      ((kerPow t k ⊔ (LinearMap.range t ⊓ kerPow t (k + 1))).comap
        (kerPow t (k + 1)).subtype).map (kerQuotientMk t k) ∧
    LinearMap.range (kerToRangeQuotient t k) =
      ((rangePow t (k + 1) ⊔ (kerPow t (k + 1)).map (t ^ k)).comap
        (rangePow t k).subtype).map (rangeQuotientMk t k) ∧
    Function.Injective (kerQuotientShift t k) ∧
    LinearMap.range (kerQuotientShift t k) =
      ((kerPow t k ⊔ (kerPow t (k + 2)).map t).comap
        (kerPow t (k + 1)).subtype).map (kerQuotientMk t k) ∧
    LinearMap.range (kerQuotientShift t k) =
      ((kerPow t k ⊔ (LinearMap.range t ⊓ kerPow t (k + 1))).comap
        (kerPow t (k + 1)).subtype).map (kerQuotientMk t k) ∧
    Function.Surjective (rangeQuotientShift t k) ∧
    LinearMap.ker (rangeQuotientShift t k) =
      ((rangePow t (k + 1) ⊔ (kerPow t (k + 1)).map (t ^ k)).comap
        (rangePow t k).subtype).map (rangeQuotientMk t k) ∧
    LinearMap.range (kerQuotientShift t k) =
      LinearMap.ker (kerToRangeQuotient t k) ∧
    LinearMap.range (kerToRangeQuotient t k) =
      LinearMap.ker (rangeQuotientShift t k)

/-- All ten assertions for every module over an arbitrary ring and every
natural index, with independent coefficient and carrier universes. -/
def PowerQuotientExactSequenceStatement : Prop :=
  ∀ (R : Type uR) [Ring R] (V : Type uV) [AddCommGroup V] [Module R V]
    (t : Module.End R V) (k : ℕ), PowerQuotientExactnessAt t k

/-- The explicit source specialization to an arbitrary complex vector space. -/
def ComplexPowerQuotientExactSequenceStatement : Prop :=
  ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (t : Module.End ℂ V) (k : ℕ), PowerQuotientExactnessAt t k

/-- The ring-general exact-sequence assertions and their complex specialization. -/
def PowerQuotientExactSequenceStatements : Prop :=
  PowerQuotientExactSequenceStatement.{uR, uV} ∧
    ComplexPowerQuotientExactSequenceStatement.{uV}

end Langlands.LinearAlgebra.StableEndomorphism
