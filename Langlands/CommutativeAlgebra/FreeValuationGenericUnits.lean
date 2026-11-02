import Langlands.CommutativeAlgebra.FreeValuationAlgebraSaturation
import Mathlib.RingTheory.Localization.Basic

/-! # Units in scalar localizations of free valuation algebras -/

noncomputable section

open scoped nonZeroDivisors

universe u v w

namespace Langlands.CommutativeAlgebra

variable {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
variable {A : Type v} [CommRing A] [Algebra R A] [Module.Free R A]

/-- A primitive divisor of a nonzero base scalar is a unit. -/
theorem isUnit_of_dvd_scalar_of_free_of_closedFibrePrime
    (hp : ((IsLocalRing.maximalIdeal R).map (algebraMap R A)).IsPrime)
    {a : A} (ha : a ∉ (IsLocalRing.maximalIdeal R).map (algebraMap R A))
    {r : R} (hr : r ≠ 0) (h : a ∣ algebraMap R A r) : IsUnit a := by
  obtain ⟨b, hb⟩ := h
  have hdiv : algebraMap R A r ∣ a * b := by rw [← hb]
  obtain ⟨c, hc⟩ :=
    (scalar_dvd_iff_mul_dvd_of_free_of_closedFibrePrime hp ha r).mp hdiv
  refine isUnit_iff_exists_inv.mpr ⟨c, ?_⟩
  apply smul_right_injective A hr
  simp only [Algebra.smul_def]
  calc
    algebraMap R A r * (a * c) = a * (algebraMap R A r * c) := by ring
    _ = a * b := by rw [← hc]
    _ = algebraMap R A r := hb.symm
    _ = algebraMap R A r * 1 := (mul_one _).symm

variable {B : Type w} [CommRing B] [Algebra A B]
variable [IsLocalization (Algebra.algebraMapSubmonoid A R⁰) B]

include R in
omit [ValuationRing R] in
/-- The scalar localization of a free module algebra is faithful. -/
theorem scalarLocalization_injective_of_free : Function.Injective (algebraMap A B) := by
  intro a b hab
  obtain ⟨c, hc⟩ := IsLocalization.exists_of_eq
    (M := Algebra.algebraMapSubmonoid A R⁰) hab
  obtain ⟨r, hr, he⟩ := c.property
  have hr0 : r ≠ 0 := nonZeroDivisors.ne_zero hr
  change (c : A) * a = (c : A) * b at hc
  rw [← he, ← Algebra.smul_def, ← Algebra.smul_def] at hc
  exact smul_right_injective A hr0 hc

/-- A primitive element that is a generic unit is already a total unit. -/
theorem isUnit_scalarLocalization_iff_of_free_of_closedFibrePrime
    (hp : ((IsLocalRing.maximalIdeal R).map (algebraMap R A)).IsPrime)
    {a : A} (ha : a ∉ (IsLocalRing.maximalIdeal R).map (algebraMap R A)) :
    IsUnit (algebraMap A B a) ↔ IsUnit a := by
  constructor
  · intro h
    obtain ⟨s, hs, hdiv⟩ :=
      (IsLocalization.algebraMap_isUnit_iff
        (M := Algebra.algebraMapSubmonoid A R⁰)).mp h
    obtain ⟨r, hr, rfl⟩ := hs
    exact isUnit_of_dvd_scalar_of_free_of_closedFibrePrime hp ha
      (nonZeroDivisors.ne_zero hr) hdiv
  · exact fun h => h.map (algebraMap A B)

/-- Every unit of the scalar localization has a nonzero scalar denominator and
is, after clearing it, a nonzero scalar times the image of a total unit. -/
theorem exists_scalar_unit_decomposition_of_free_of_closedFibrePrime
    (hp : ((IsLocalRing.maximalIdeal R).map (algebraMap R A)).IsPrime)
    (b : Bˣ) :
    ∃ (r d : R) (a : Aˣ), r ≠ 0 ∧ d ≠ 0 ∧
      algebraMap A B (algebraMap R A r) * (b : B) =
        algebraMap A B (algebraMap R A d) * algebraMap A B (a : A) := by
  have hA : (1 : A) ≠ 0 := by
    intro h
    apply hp.one_notMem
    rw [h]
    exact Ideal.zero_mem _
  let : Nontrivial A := nontrivial_of_ne 1 0 hA
  have hinj := scalarLocalization_injective_of_free (R := R) (A := A) (B := B)
  let : Nontrivial B := nontrivial_of_ne
    (algebraMap A B 1) (algebraMap A B 0) (fun h => hA (hinj h))
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj
    (Algebra.algebraMapSubmonoid A R⁰) (b : B)
  have hau : IsUnit (algebraMap A B a) := by
    rw [← hs]
    exact b.isUnit.mul (IsLocalization.map_units B s)
  have ha : a ≠ 0 := by
    intro h
    exact hau.ne_zero (by rw [h, map_zero])
  obtain ⟨d, a₀, hd, hnorm, ha₀⟩ :=
    exists_scalar_normalization_not_mem (R := R) ha
  rw [Ideal.smul_top_eq_map] at ha₀
  have ha₀u : IsUnit (algebraMap A B a₀) := by
    apply isUnit_of_mul_isUnit_right (x := algebraMap A B (algebraMap R A d))
    simpa only [hnorm, Algebra.smul_def, map_mul] using hau
  obtain ⟨a', ha'⟩ :=
    (isUnit_scalarLocalization_iff_of_free_of_closedFibrePrime hp ha₀).mp ha₀u
  obtain ⟨r, hr, her⟩ := s.property
  refine ⟨r, d, a', nonZeroDivisors.ne_zero hr, hd, ?_⟩
  calc
    algebraMap A B (algebraMap R A r) * (b : B) =
        (b : B) * algebraMap A B s := by rw [her, mul_comm]
    _ = algebraMap A B a := hs
    _ = algebraMap A B (algebraMap R A d) * algebraMap A B (a' : A) := by
      rw [hnorm, Algebra.smul_def, map_mul, ha']

/-- Actual data for a scalar-times-unit expression, recorded after clearing a
nonzero base denominator. -/
structure ScalarUnitDecomposition (R : Type u) [CommRing R]
    (A : Type v) [CommRing A] [Algebra R A]
    (B : Type w) [CommRing B] [Algebra A B] (b : Bˣ) where
  denominator : R
  numerator : R
  totalUnit : Aˣ
  denominator_ne_zero : denominator ≠ 0
  numerator_ne_zero : numerator ≠ 0
  cleared_eq : algebraMap A B (algebraMap R A denominator) * (b : B) =
    algebraMap A B (algebraMap R A numerator) * algebraMap A B (totalUnit : A)

/-- Choose a scalar-times-unit decomposition of an arbitrary unit of the
scalar localization of a free valuation algebra with integral closed fibre. -/
noncomputable def scalarUnitDecompositionOfFree
    (hp : ((IsLocalRing.maximalIdeal R).map (algebraMap R A)).IsPrime)
    (b : Bˣ) : ScalarUnitDecomposition R A B b :=
  Classical.choice (by
    obtain ⟨r, d, a, hr, hd, h⟩ :=
      exists_scalar_unit_decomposition_of_free_of_closedFibrePrime hp b
    exact ⟨⟨r, d, a, hr, hd, h⟩⟩)

end Langlands.CommutativeAlgebra
