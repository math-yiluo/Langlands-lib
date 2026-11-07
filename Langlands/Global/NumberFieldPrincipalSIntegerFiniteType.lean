import Langlands.Global.DedekindAwaySInteger
import Langlands.Global.AdelicSIntegersDiagram
import Mathlib.RingTheory.Localization.Away.AdjoinRoot

/-! # Cofinal actual number-field integer rings of finite type over the integers -/

noncomputable section

universe u

open IsDedekindDomain
open scoped BigOperators

namespace Langlands.Global

variable (K : Type u) [Field K] [NumberField K]

/-- The actual finite set of places where the inverse of an integral denominator
is not integral. -/
def numberFieldPrincipalExceptional (t : NumberField.RingOfIntegers K) :
    Finset (FinitePlace K) := by
  classical
  exact (HeightOneSpectrum.Support.finite (NumberField.RingOfIntegers K) (t : K)⁻¹).toFinset

@[simp]
theorem mem_numberFieldPrincipalExceptional
    (t : NumberField.RingOfIntegers K) (ht : t ≠ 0) (p : FinitePlace K) :
    p ∈ numberFieldPrincipalExceptional K t ↔ t ∈ p.asIdeal := by
  classical
  rw [numberFieldPrincipalExceptional, Set.Finite.mem_toFinset]
  change 1 < p.valuation K ((t : K)⁻¹) ↔ t ∈ p.asIdeal
  rw [map_inv₀, one_lt_inv₀, p.valuation_lt_one_iff_mem]
  exact pos_iff_ne_zero.mpr ((map_ne_zero (p.valuation K)).mpr (by
    intro h
    exact ht (Subtype.ext h)))

/-- The actual principal outside-set ring agrees with the original embedded
localization, preserving every field element and its integer coefficients. -/
def numberFieldPrincipalSIntegerEquiv
    (t : NumberField.RingOfIntegers K) (ht : t ≠ 0) :
    dedekindAwaySubalgebra (K := K) t ht ≃ₐ[NumberField.RingOfIntegers K]
      ((numberFieldPrincipalExceptional K t : Finset (FinitePlace K)) :
        Set (FinitePlace K)).integer K :=
  Subalgebra.equivOfEq _ _ (by
    ext x
    rw [mem_dedekindAwaySubalgebra_iff t ht]
    change (∀ p : FinitePlace K, t ∉ p.asIdeal → p.valuation K x ≤ 1) ↔
      (∀ p : FinitePlace K,
        p ∉ numberFieldPrincipalExceptional K t → p.valuation K x ≤ 1)
    simp only [mem_numberFieldPrincipalExceptional K t ht])

@[simp]
theorem numberFieldPrincipalSIntegerEquiv_coe
    (t : NumberField.RingOfIntegers K) (ht : t ≠ 0)
    (x : dedekindAwaySubalgebra (K := K) t ht) :
    (numberFieldPrincipalSIntegerEquiv K t ht x : K) = x := by
  rfl

namespace NumberFieldPrincipalSIntegers

variable (t : NumberField.RingOfIntegers K) [Fact (t ≠ 0)]

/-- Finite type of the actual principal outside-set integer ring over the
original integers, transported through the elementwise localization comparison. -/
scoped instance finiteType : Algebra.FiniteType ℤ
    (((numberFieldPrincipalExceptional K t : Finset (FinitePlace K)) :
      Set (FinitePlace K)).integer K) := by
  let D := dedekindAwaySubalgebra (K := K) t (Fact.out : t ≠ 0)
  let : IsLocalization (Submonoid.powers t) D :=
    Localization.subalgebra.isLocalization_ofField K _ _
  let : Algebra.FinitePresentation (NumberField.RingOfIntegers K) D :=
    IsLocalization.Away.finitePresentation t
  have h : Algebra.FiniteType (NumberField.RingOfIntegers K)
      (((numberFieldPrincipalExceptional K t : Finset (FinitePlace K)) :
        Set (FinitePlace K)).integer K) :=
    (inferInstance : Algebra.FiniteType (NumberField.RingOfIntegers K) D).equiv
      (numberFieldPrincipalSIntegerEquiv K t Fact.out)
  exact (inferInstance : Algebra.FiniteType ℤ (NumberField.RingOfIntegers K)).trans h

end NumberFieldPrincipalSIntegers

/-- Every finite set of actual finite places is contained in one of the
principal exceptional sets. No class-number choice is needed. -/
theorem exists_numberFieldPrincipalExceptional_superset
    (S : Finset (FinitePlace K)) :
    ∃ t : NumberField.RingOfIntegers K, t ≠ 0 ∧
      S ⊆ numberFieldPrincipalExceptional K t := by
  classical
  have H : ∀ p : S, ∃ a : NumberField.RingOfIntegers K,
      a ≠ 0 ∧ a ∈ p.1.asIdeal := by
    intro p
    obtain ⟨a, ha, ha0⟩ := (Submodule.ne_bot_iff p.1.asIdeal).mp p.1.ne_bot
    exact ⟨a, ha0, ha⟩
  choose a ha0 ha using H
  let t : NumberField.RingOfIntegers K := ∏ p : S, a p
  have ht : t ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p _ => ha0 p
  refine ⟨t, ht, ?_⟩
  intro p hp
  apply (mem_numberFieldPrincipalExceptional K t ht p).mpr
  exact Ideal.IsPrime.prod_mem_iff.mpr ⟨⟨p, hp⟩, Finset.mem_univ _, ha ⟨p, hp⟩⟩

/-- Choose a nonzero integral denominator whose actual principal exceptional
set contains the prescribed initial places. -/
def numberFieldPrincipalDenominator (S : Finset (FinitePlace K)) :
    {t : NumberField.RingOfIntegers K // t ≠ 0 ∧
      S ⊆ numberFieldPrincipalExceptional K t} :=
  ⟨(exists_numberFieldPrincipalExceptional_superset K S).choose,
    (exists_numberFieldPrincipalExceptional_superset K S).choose_spec⟩

/-- An actual integer level above any prescribed finite initial set. -/
def numberFieldPrincipalLevelAbove (S : Finset (FinitePlace K)) :
    AdelicLevelIndexAbove S :=
  ⟨numberFieldPrincipalExceptional K (numberFieldPrincipalDenominator K S).1,
    (numberFieldPrincipalDenominator K S).2.2⟩

open scoped NumberFieldPrincipalSIntegers

/-- The chosen actual cofinal integer level is of finite type over the integers. -/
instance numberFieldPrincipalLevelAbove_finiteType (S : Finset (FinitePlace K)) :
    Algebra.FiniteType ℤ
      ((((numberFieldPrincipalLevelAbove K S).val : Finset (FinitePlace K)) :
        Set (FinitePlace K)).integer K) := by
  let : Fact ((numberFieldPrincipalDenominator K S).1 ≠ 0) :=
    ⟨(numberFieldPrincipalDenominator K S).2.1⟩
  exact inferInstanceAs (Algebra.FiniteType ℤ
    (((numberFieldPrincipalExceptional K (numberFieldPrincipalDenominator K S).1 :
      Finset (FinitePlace K)) : Set (FinitePlace K)).integer K))

end Langlands.Global
