import Langlands.CommutativeAlgebra.FreeValuationGenericUnits
import Mathlib.RingTheory.Flat.TorsionFree

/-! # Primitive normalization and generic units for projective valuation algebras -/

noncomputable section

open scoped nonZeroDivisors

universe u v w

namespace Langlands.CommutativeAlgebra

variable {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R]

/-- Primitive scalar normalization passes from a free module to a projective
direct summand, with no finite-generation assumption on the module. -/
theorem exists_scalar_normalization_of_projective
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Projective R M]
    {x : M} (hx : x ≠ 0) :
    ∃ (r : R) (y : M) (l : M →ₗ[R] R), r ≠ 0 ∧ x = r • y ∧ l y = 1 := by
  obtain ⟨s, hs⟩ := Module.projective_def.mp
    (inferInstance : Module.Projective R M)
  let p : (M →₀ R) →ₗ[R] M := Finsupp.linearCombination R id
  have hps (z : M) : p (s z) = z := hs z
  have hsx : s x ≠ 0 := by
    intro h
    apply hx
    apply hs.injective
    simpa using h
  obtain ⟨r, y, l, hr, hxy, hl⟩ :=
    exists_scalar_normalization_of_free (R := R) hsx
  have hsp : s (p y) = y := by
    apply smul_right_injective (M →₀ R) hr
    calc
      r • s (p y) = s (p (r • y)) := by simp only [map_smul]
      _ = s (p (s x)) := by rw [← hxy]
      _ = s x := by rw [hps]
      _ = r • y := hxy
  refine ⟨r, p y, l.comp s, hr, ?_, ?_⟩
  · calc
      x = p (s x) := (hps x).symm
      _ = r • p y := by rw [hxy, map_smul]
  · simpa only [LinearMap.comp_apply, hsp] using hl

/-- Choose primitive scalar normalization data in a projective module. -/
noncomputable def scalarNormalizationOfProjective
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Projective R M]
    {x : M} (hx : x ≠ 0) : ScalarNormalization R M x :=
  Classical.choice (by
    obtain ⟨r, y, l, hr, hxy, hl⟩ :=
      exists_scalar_normalization_of_projective (R := R) hx
    exact ⟨⟨r, y, l, hr, hxy, hl⟩⟩)

/-- A projective-module normalization is nonzero modulo the maximal ideal. -/
theorem exists_scalar_normalization_not_mem_of_projective
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Projective R M]
    {x : M} (hx : x ≠ 0) :
    ∃ (r : R) (y : M), r ≠ 0 ∧ x = r • y ∧
      y ∉ IsLocalRing.maximalIdeal R • (⊤ : Submodule R M) := by
  let n := scalarNormalizationOfProjective (R := R) hx
  refine ⟨n.scalar, n.vector, n.scalar_ne_zero, n.eq_smul, ?_⟩
  intro hy
  have hm := Submodule.smul_top_le_comap_smul_top
    (IsLocalRing.maximalIdeal R) n.functional hy
  change n.functional n.vector ∈ IsLocalRing.maximalIdeal R • (⊤ : Ideal R) at hm
  rw [Ideal.smul_eq_mul, Ideal.mul_top, n.functional_vector] at hm
  exact hm isUnit_one

variable {A : Type v} [CommRing A] [Algebra R A] [Module.Projective R A]

/-- Multiplication by an element nonzero on the integral closed fibre preserves
and reflects divisibility by every base scalar in a projective valuation algebra. -/
theorem scalar_dvd_iff_mul_dvd_of_projective_of_closedFibrePrime
    (hp : ((IsLocalRing.maximalIdeal R).map (algebraMap R A)).IsPrime)
    {s a : A} (hs : s ∉ (IsLocalRing.maximalIdeal R).map (algebraMap R A)) (r : R) :
    algebraMap R A r ∣ s * a ↔ algebraMap R A r ∣ a := by
  constructor
  · rintro ⟨z, hz⟩
    by_cases ha : a = 0
    · simp [ha]
    obtain ⟨d, a₀, hd, hnorm, ha₀⟩ :=
      exists_scalar_normalization_not_mem_of_projective (R := R) ha
    have ha₀' : a₀ ∉ (IsLocalRing.maximalIdeal R).map (algebraMap R A) := by
      rw [Ideal.smul_top_eq_map] at ha₀
      exact ha₀
    rcases ValuationRing.dvd_total r d with hrd | hdr
    · obtain ⟨t, ht⟩ := hrd
      refine ⟨t • a₀, ?_⟩
      rw [hnorm, ht, mul_smul, Algebra.smul_def]
    · obtain ⟨t, ht⟩ := hdr
      have hcancel : t • z = s * a₀ := by
        apply smul_right_injective A hd
        calc
          d • (t • z) = algebraMap R A r * z := by
            rw [← mul_smul, ← ht, Algebra.smul_def]
          _ = s * a := hz.symm
          _ = d • (s * a₀) := by rw [hnorm, mul_smul_comm]
      have htunit : IsUnit t := by
        by_contra h
        have htm : t ∈ IsLocalRing.maximalIdeal R := h
        have hm : t • z ∈ (IsLocalRing.maximalIdeal R).map (algebraMap R A) := by
          rw [Algebra.smul_def]
          exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ htm)
        rw [hcancel] at hm
        exact (hp.mem_or_mem hm).elim hs ha₀'
      obtain ⟨t', htt'⟩ := htunit.exists_right_inv
      refine ⟨t' • a₀, ?_⟩
      rw [← Algebra.smul_def, ht, mul_smul, smul_smul t t', htt', one_smul]
      exact hnorm
  · intro h
    exact dvd_mul_of_dvd_right h _

/-- A primitive divisor of a nonzero base scalar in a projective valuation
algebra with integral closed fibre is a unit. -/
theorem isUnit_of_dvd_scalar_of_projective_of_closedFibrePrime
    (hp : ((IsLocalRing.maximalIdeal R).map (algebraMap R A)).IsPrime)
    {a : A} (ha : a ∉ (IsLocalRing.maximalIdeal R).map (algebraMap R A))
    {r : R} (hr : r ≠ 0) (h : a ∣ algebraMap R A r) : IsUnit a := by
  obtain ⟨b, hb⟩ := h
  have hdiv : algebraMap R A r ∣ a * b := by rw [← hb]
  obtain ⟨c, hc⟩ :=
    (scalar_dvd_iff_mul_dvd_of_projective_of_closedFibrePrime hp ha r).mp hdiv
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
/-- Localization at nonzero base scalars is injective for projective algebras. -/
theorem scalarLocalization_injective_of_projective :
    Function.Injective (algebraMap A B) := by
  intro a b hab
  obtain ⟨c, hc⟩ := IsLocalization.exists_of_eq
    (M := Algebra.algebraMapSubmonoid A R⁰) hab
  obtain ⟨r, hr, he⟩ := c.property
  have hr0 : r ≠ 0 := nonZeroDivisors.ne_zero hr
  change (c : A) * a = (c : A) * b at hc
  rw [← he, ← Algebra.smul_def, ← Algebra.smul_def] at hc
  exact smul_right_injective A hr0 hc

/-- A primitive generic unit in a projective valuation algebra with integral
closed fibre is already a total unit. -/
theorem isUnit_scalarLocalization_iff_of_projective_of_closedFibrePrime
    (hp : ((IsLocalRing.maximalIdeal R).map (algebraMap R A)).IsPrime)
    {a : A} (ha : a ∉ (IsLocalRing.maximalIdeal R).map (algebraMap R A)) :
    IsUnit (algebraMap A B a) ↔ IsUnit a := by
  constructor
  · intro h
    obtain ⟨s, hs, hdiv⟩ :=
      (IsLocalization.algebraMap_isUnit_iff
        (M := Algebra.algebraMapSubmonoid A R⁰)).mp h
    obtain ⟨r, hr, rfl⟩ := hs
    exact isUnit_of_dvd_scalar_of_projective_of_closedFibrePrime hp ha
      (nonZeroDivisors.ne_zero hr) hdiv
  · exact fun h => h.map (algebraMap A B)

/-- Every generic unit in a projective valuation algebra with integral closed
fibre is a scalar times a total unit, after clearing a nonzero base denominator. -/
theorem exists_scalar_unit_decomposition_of_projective_of_closedFibrePrime
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
  have hinj := scalarLocalization_injective_of_projective (R := R) (A := A) (B := B)
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
    exists_scalar_normalization_not_mem_of_projective (R := R) ha
  rw [Ideal.smul_top_eq_map] at ha₀
  have ha₀u : IsUnit (algebraMap A B a₀) := by
    apply isUnit_of_mul_isUnit_right (x := algebraMap A B (algebraMap R A d))
    simpa only [hnorm, Algebra.smul_def, map_mul] using hau
  obtain ⟨a', ha'⟩ :=
    (isUnit_scalarLocalization_iff_of_projective_of_closedFibrePrime hp ha₀).mp ha₀u
  obtain ⟨r, hr, her⟩ := s.property
  refine ⟨r, d, a', nonZeroDivisors.ne_zero hr, hd, ?_⟩
  calc
    algebraMap A B (algebraMap R A r) * (b : B) =
        (b : B) * algebraMap A B s := by rw [her, mul_comm]
    _ = algebraMap A B a := hs
    _ = algebraMap A B (algebraMap R A d) * algebraMap A B (a' : A) := by
      rw [hnorm, Algebra.smul_def, map_mul, ha']

/-- Choose actual scalar-times-unit data for a generic unit of a projective
valuation algebra with integral closed fibre. -/
noncomputable def scalarUnitDecompositionOfProjective
    (hp : ((IsLocalRing.maximalIdeal R).map (algebraMap R A)).IsPrime)
    (b : Bˣ) : ScalarUnitDecomposition R A B b :=
  Classical.choice (by
    obtain ⟨r, d, a, hr, hd, h⟩ :=
      exists_scalar_unit_decomposition_of_projective_of_closedFibrePrime hp b
    exact ⟨⟨r, d, a, hr, hd, h⟩⟩)

end Langlands.CommutativeAlgebra
