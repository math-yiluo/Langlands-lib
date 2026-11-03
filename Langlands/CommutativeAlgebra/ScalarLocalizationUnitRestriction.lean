import Langlands.CommutativeAlgebra.ProjectiveValuationGenericUnits

/-! # Descent of scalar-localization units through a closed-fibre restriction -/

noncomputable section

open scoped nonZeroDivisors

universe u v w x y

namespace Langlands.CommutativeAlgebra

section Local

variable {R : Type u} [CommRing R] [IsLocalRing R]
    {C : Type x} [CommRing C] [Algebra R C]

/-- An algebra with nonempty closed fibre reflects units of its local base. -/
theorem isUnit_of_algebraMap_isUnit_of_closedFibre_ne_top
    (hC : (IsLocalRing.maximalIdeal R).map (algebraMap R C) ≠ ⊤)
    {r : R} (hr : IsUnit (algebraMap R C r)) : IsUnit r := by
  by_contra h
  exact hC (Ideal.eq_top_of_isUnit_mem _
    (Ideal.mem_map_of_mem _ (show r ∈ IsLocalRing.maximalIdeal R from h)) hr)

end Local

section Valuation

variable {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
    {C : Type x} [CommRing C] [Algebra R C] [Module.IsTorsionFree R C]

/-- Scalar multiples of total units determine the scalar up to a base unit,
provided the comparison algebra still has nonempty closed fibre. -/
theorem exists_baseUnit_of_smul_units_eq
    (hC : (IsLocalRing.maximalIdeal R).map (algebraMap R C) ≠ ⊤)
    {r d : R} (hr : r ≠ 0) (hd : d ≠ 0) (c e : Cˣ)
    (h : r • (c : C) = d • (e : C)) :
    ∃ t : Rˣ, d = r * (t : R) := by
  rcases ValuationRing.dvd_total r d with hrd | hdr
  · obtain ⟨t, ht⟩ := hrd
    have hc : (c : C) = t • (e : C) := by
      apply smul_right_injective C hr
      simpa only [ht, mul_smul] using h
    have htC : IsUnit (algebraMap R C t) := by
      apply isUnit_of_mul_isUnit_left (y := (e : C))
      rw [← Algebra.smul_def, ← hc]
      exact c.isUnit
    obtain ⟨t', ht'⟩ :=
      isUnit_of_algebraMap_isUnit_of_closedFibre_ne_top hC htC
    exact ⟨t', by simpa only [ht'] using ht⟩
  · obtain ⟨t, ht⟩ := hdr
    have he : t • (c : C) = (e : C) := by
      apply smul_right_injective C hd
      simpa only [ht, mul_smul] using h
    have htC : IsUnit (algebraMap R C t) := by
      apply isUnit_of_mul_isUnit_left (y := (c : C))
      rw [← Algebra.smul_def, he]
      exact e.isUnit
    obtain ⟨t', ht'⟩ :=
      isUnit_of_algebraMap_isUnit_of_closedFibre_ne_top hC htC
    refine ⟨t'⁻¹, ?_⟩
    rw [ht, ← ht', mul_assoc, Units.mul_inv, mul_one]

variable {D : Type y} [CommRing D] [Algebra C D]
    [IsLocalization (Algebra.algebraMapSubmonoid C R⁰) D]

include R in
omit [ValuationRing R] in
/-- Torsionfreeness suffices for injectivity of localization at base scalars. -/
theorem scalarLocalization_injective_of_torsionFree :
    Function.Injective (algebraMap C D) := by
  intro a b hab
  obtain ⟨s, hs⟩ := IsLocalization.exists_of_eq
    (M := Algebra.algebraMapSubmonoid C R⁰) hab
  obtain ⟨r, hr, he⟩ := s.property
  change (s : C) * a = (s : C) * b at hs
  rw [← he, ← Algebra.smul_def, ← Algebra.smul_def] at hs
  exact smul_right_injective C (nonZeroDivisors.ne_zero hr) hs

variable {A : Type v} [CommRing A] [Algebra R A] [Module.Projective R A]
    {B : Type w} [CommRing B] [Algebra A B]
    [IsLocalization (Algebra.algebraMapSubmonoid A R⁰) B]

/-- A generic unit that becomes a total unit after a closed-fibre-preserving
restriction already lifts to a total unit. -/
theorem exists_unit_of_scalarLocalization_restriction
    (hp : ((IsLocalRing.maximalIdeal R).map (algebraMap R A)).IsPrime)
    (hC : (IsLocalRing.maximalIdeal R).map (algebraMap R C) ≠ ⊤)
    (f : A →ₐ[R] C) (g : B →+* D)
    (hfg : ∀ a : A, g (algebraMap A B a) = algebraMap C D (f a))
    (b : Bˣ) (c : Cˣ) (hc : g (b : B) = algebraMap C D (c : C)) :
    ∃ a : Aˣ, algebraMap A B (a : A) = (b : B) := by
  let n := scalarUnitDecompositionOfProjective (B := B) hp b
  let e : Cˣ := Units.map f.toMonoidHom n.totalUnit
  have h : n.denominator • (c : C) = n.numerator • (e : C) := by
    apply scalarLocalization_injective_of_torsionFree (R := R) (D := D)
    simp only [Algebra.smul_def]
    change algebraMap C D (algebraMap R C n.denominator * (c : C)) =
      algebraMap C D (algebraMap R C n.numerator * f (n.totalUnit : A))
    have h' := congrArg g n.cleared_eq
    simpa only [map_mul, hfg, f.commutes, hc] using h'
  obtain ⟨t, ht⟩ := exists_baseUnit_of_smul_units_eq hC
    n.denominator_ne_zero n.numerator_ne_zero c e h
  refine ⟨Units.map (algebraMap R A).toMonoidHom t * n.totalUnit, ?_⟩
  change algebraMap A B (algebraMap R A (t : R) * (n.totalUnit : A)) = (b : B)
  have hu : IsUnit (algebraMap A B (algebraMap R A n.denominator)) :=
    IsLocalization.map_units (M := Algebra.algebraMapSubmonoid A R⁰) B
      ⟨algebraMap R A n.denominator,
        ⟨n.denominator, mem_nonZeroDivisors_iff_ne_zero.mpr n.denominator_ne_zero,
          rfl⟩⟩
  apply hu.mul_left_cancel
  calc
    algebraMap A B (algebraMap R A n.denominator) *
        algebraMap A B (algebraMap R A (t : R) * (n.totalUnit : A)) =
      algebraMap A B (algebraMap R A n.numerator) *
        algebraMap A B (n.totalUnit : A) := by
          simp only [ht, map_mul]
          ring
    _ = algebraMap A B (algebraMap R A n.denominator) * (b : B) :=
      n.cleared_eq.symm

/-- Choose the actual total unit detected after restriction, retaining the
equality with the given generic unit as part of the result. -/
def scalarLocalizationUnitOfRestriction
    (hp : ((IsLocalRing.maximalIdeal R).map (algebraMap R A)).IsPrime)
    (hC : (IsLocalRing.maximalIdeal R).map (algebraMap R C) ≠ ⊤)
    (f : A →ₐ[R] C) (g : B →+* D)
    (hfg : ∀ a : A, g (algebraMap A B a) = algebraMap C D (f a))
    (b : Bˣ) (c : Cˣ) (hc : g (b : B) = algebraMap C D (c : C)) :
    {a : Aˣ // algebraMap A B (a : A) = (b : B)} :=
  ⟨Classical.choose (exists_unit_of_scalarLocalization_restriction hp hC f g hfg b c hc),
    Classical.choose_spec (exists_unit_of_scalarLocalization_restriction hp hC f g hfg b c hc)⟩

end Valuation

end Langlands.CommutativeAlgebra
