import Langlands.Global.ArithmeticSIntegerExtension
import Langlands.Global.CurvePlaceIntegralLattice
import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
import Mathlib.Algebra.Polynomial.Lifts

noncomputable section

universe u

open scoped Langlands.Global.CurvePlaceCompletionExtension

namespace Langlands.Global

variable {k K L : Type u} [Field k] [Field K] [Field L]
  [Algebra k K] [Algebra k L] [Algebra K L]
  [IsScalarTower k K L] [FiniteDimensional K L] [Finite k]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
  (S : Finset (AlgebraicCurve.Place k K))

/-- Every coefficient of the original minimal polynomial lies in the lower outside-S ring. -/
theorem curvePlaceSIntegers_minpoly_coeff_mem (x : L)
    (hx : x ∈ curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L) S))
    (n : ℕ) : (minpoly K x).coeff n ∈ curvePlaceSIntegers k K S := by
  intro p hp
  have hl : IsIntegral p.toValuationSubring x :=
    (CurvePlaceIntegralLattice.integral_mem_iff p x).mpr fun q => by
      have hr : curvePlaceRestriction q.1 = p :=
        (curvePlaceRestriction_eq_iff _ _).mpr q.2
      exact hx q.1 (by simpa [hr] using hp)
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' K hl, Polynomial.coeff_map]
  exact ((minpoly p.toValuationSubring x).coeff n).property

/-- The full upper-preimage ring is exactly the actual lower integral closure. -/
theorem curvePlaceSIntegers_integralClosure_eq :
    (integralClosure (curvePlaceSIntegers k K S) L).toSubring =
      curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L) S) := by
  apply le_antisymm (curvePlaceSIntegers_integralClosure_le S)
  intro x hx
  let R := curvePlaceSIntegers k K S
  have hlifts : minpoly K x ∈ Polynomial.lifts (algebraMap R K) :=
    (Polynomial.lifts_iff_coeff_lifts _).mpr fun n =>
      ⟨⟨_, curvePlaceSIntegers_minpoly_coeff_mem S x hx n⟩, rfl⟩
  obtain ⟨f, hf⟩ := (Polynomial.mem_lifts _).mp hlifts
  have hxK : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  refine ⟨f, Polynomial.monic_of_injective R.subtype_injective (hf ▸ minpoly.monic hxK), ?_⟩
  change Polynomial.aeval x f = 0
  rw [← Polynomial.aeval_map_algebraMap K x, hf]
  exact minpoly.aeval K x

/-- Identity on original upper-field elements identifies upper integers with the integral closure. -/
def curvePlaceSIntegersIntegralClosureEquiv :
    integralClosure (curvePlaceSIntegers k K S) L ≃+*
      curvePlaceSIntegers k L (curvePlaceExceptionalPreimage (L := L) S) :=
  RingEquiv.subringCongr (curvePlaceSIntegers_integralClosure_eq S)

@[simp]
theorem curvePlaceSIntegersIntegralClosureEquiv_coe
    (x : integralClosure (curvePlaceSIntegers k K S) L) :
    (curvePlaceSIntegersIntegralClosureEquiv S x : L) = x := rfl

end Langlands.Global
