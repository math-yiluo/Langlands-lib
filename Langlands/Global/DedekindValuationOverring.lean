/-
The center nonzeroness and localization inclusion arguments generalize the
corresponding CurveModel proofs in
Langlands.AnthropicFLT.Definitions.Def_JacJ1_ChartAlgebra, ported from
Anthropic's Lean formalization of Fermat's Last Theorem, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, Copyright 2026 Anthropic, PBC,
under Apache-2.0. See licenses/Anthropic-FLT/LICENSE, NOTICE and ATTRIBUTION.md.
Modified by Worker 208: arbitrary Dedekind domain and original fraction field,
the actual maximal-ideal contraction under a compatible algebra, independent
universes, and the original A-algebra localization comparison.
-/
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Valuation.LocalSubring

noncomputable section

universe u v

open IsDedekindDomain

namespace Langlands.Global.DedekindValuationOverring

variable (A : Type u) (K : Type v) [CommRing A] [IsDedekindDomain A]
  [Field K] [Algebra A K] [IsFractionRing A K]
  (V : ValuationSubring K) [Algebra A V] [IsScalarTower A V K]

/-- The actual center of an original valuation overring on the original Dedekind ring. -/
def center : Ideal A := (IsLocalRing.maximalIdeal V).under A

private instance center_isPrime : (center A K V).IsPrime := by
  change ((IsLocalRing.maximalIdeal V).under A).IsPrime
  infer_instance

omit [IsDedekindDomain A] [IsFractionRing A K] in
private theorem valuation_le_one (a : A) : V.valuation (algebraMap A K a) ≤ 1 := by
  rw [IsScalarTower.algebraMap_apply A V K]
  exact (V.valuation_le_one_iff _).mpr (algebraMap A V a).property

omit [IsDedekindDomain A] [IsFractionRing A K] in
private theorem valuation_eq_one_of_notMem (a : A) (ha : a ∉ center A K V) :
    V.valuation (algebraMap A K a) = 1 := by
  change algebraMap A V a ∉ IsLocalRing.maximalIdeal V at ha
  rw [IsScalarTower.algebraMap_apply A V K]
  exact (V.valuation_eq_one_iff _).mp (IsLocalRing.notMem_maximalIdeal.mp ha)

/-- A nontrivial original valuation overring has a nonzero center on a fraction-field model. -/
theorem center_ne_bot (hV : V ≠ ⊤) : center A K V ≠ ⊥ := by
  intro hbot
  apply hV
  refine top_unique fun x _ => ?_
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbc : b ∉ center A K V := by rw [hbot]; simpa using hb0
  apply V.mem_of_valuation_le_one
  rw [map_div₀, valuation_eq_one_of_notMem A K V b hbc, div_one]
  exact valuation_le_one A K V a

/-- The actual height-one center prime of the original nontrivial valuation ring. -/
def prime (hV : V ≠ ⊤) : HeightOneSpectrum A :=
  ⟨center A K V, inferInstance, center_ne_bot A K V hV⟩

private theorem valuationSubringAtPrime_le (hV : V ≠ ⊤) :
    HeightOneSpectrum.valuationSubringAtPrime K (prime A K V hV) ≤ V := by
  rintro x ⟨a, b, hb, rfl⟩
  apply V.mem_of_valuation_le_one
  rw [map_mul, map_inv₀, valuation_eq_one_of_notMem A K V b hb, inv_one, mul_one]
  exact valuation_le_one A K V a

/-- Localizing at the actual center recovers the original valuation subring inside K. -/
theorem valuationSubringAtPrime_eq (hV : V ≠ ⊤) :
    HeightOneSpectrum.valuationSubringAtPrime K (prime A K V hV) = V :=
  ValuationSubring.eq_of_le_of_ne_top _ (valuationSubringAtPrime_le A K V hV) hV

/-- The center localization and the original valuation ring are the same original A-algebra. -/
def localizationEquiv (hV : V ≠ ⊤) :
    HeightOneSpectrum.valuationSubringAtPrime K (prime A K V hV) ≃ₐ[A] V :=
  { toRingEquiv := RingEquiv.subringCongr
      (congrArg ValuationSubring.toSubring (valuationSubringAtPrime_eq A K V hV))
    commutes' a := by
      apply Subtype.ext
      exact IsScalarTower.algebraMap_apply A V K a }

@[simp]
theorem localizationEquiv_coe (hV : V ≠ ⊤)
    (x : HeightOneSpectrum.valuationSubringAtPrime K (prime A K V hV)) :
    (localizationEquiv A K V hV x : K) = x := rfl

/-- The original valuation-ring algebra is the actual localization at its original center prime. -/
theorem isLocalization (hV : V ≠ ⊤) :
    IsLocalization (prime A K V hV).asIdeal.primeCompl V :=
  IsLocalization.isLocalization_of_algEquiv _ (localizationEquiv A K V hV)

end Langlands.Global.DedekindValuationOverring
