import Langlands.Geometry.Analytic.RationalFactorization.Statement
import Langlands.Geometry.Analytic.RationalLocalization
import Langlands.Geometry.Analytic.SpectrumIdealCriterionProof
import Langlands.Geometry.Analytic.SpectralPowerBoundProof

/-! # Rational factorization from spectrum-image containment -/

noncomputable section

universe u

namespace Langlands.Analytic.RationalFactorization

open StrictTateAlgebra PresentedStrictAffinoidAlgebra

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (P : PresentedStrictAffinoidAlgebra K) (m : ℕ) (g : P) (f : Fin m → P)

omit [CompleteSpace K] in
/-- The algebraic unit ideal prevents the denominator from vanishing on the locus. -/
theorem denominator_ne_zero (hunit : RationalLocalization.GeneratesUnitIdeal K P m g f)
    (x : BanachSpectrum P) (hx : x ∈ RationalLocalization.locus K P m g f) :
    x g ≠ 0 := by
  intro hg
  have hle : Ideal.span (insert g (Set.range f)) ≤ x.kernel := by
    apply Ideal.span_le.mpr
    intro a ha
    rcases ha with rfl | ⟨j, rfl⟩
    · exact hg
    · exact le_antisymm (by simpa only [hg] using hx j) (apply_nonneg x.toMulRingSeminorm (f j))
  rw [hunit] at hle
  exact x.kernel_isPrime.ne_top (top_unique hle)

/-- For actual strict affinoids, the algebraic premise is equivalent to the
source's absence of common zeros of the denominator and numerators. -/
theorem generatesUnitIdeal_iff_no_common_zero :
    RationalLocalization.GeneratesUnitIdeal K P m g f ↔
      ∀ x : BanachSpectrum P, x g ≠ 0 ∨ ∃ j, x (f j) ≠ 0 := by
  constructor
  · intro hunit x
    by_contra h
    push Not at h
    have hle : Ideal.span (insert g (Set.range f)) ≤ x.kernel := by
      apply Ideal.span_le.mpr
      intro a ha
      rcases ha with rfl | ⟨j, rfl⟩
      · exact h.1
      · exact h.2 j
    rw [hunit] at hle
    exact x.kernel_isPrime.ne_top (top_unique hle)
  · intro h
    by_contra hI
    obtain ⟨x, hx⟩ := exists_spectrum_kernel_of_proper_ideal P
      (Ideal.span (insert g (Set.range f))) hI
    rcases h x with hg | ⟨j, hj⟩
    · exact hg (hx (Ideal.subset_span (Set.mem_insert _ _)))
    · exact hj (hx (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_range_self j))))

variable (Q : PresentedStrictAffinoidAlgebra K) (φ : BoundedAlgHom K P Q)

/-- Spectrum containment forces the image denominator to be an actual unit. -/
theorem isUnit_image_denominator
    (hunit : RationalLocalization.GeneratesUnitIdeal K P m g f)
    (himage : ∀ x : BanachSpectrum Q,
      BanachSpectrum.comap φ.toBoundedRingHom x ∈ RationalLocalization.locus K P m g f) :
    IsUnit (φ g) := by
  apply (isUnit_iff_forall_spectrum_ne_zero Q (φ g)).mpr
  intro x
  exact denominator_ne_zero K P m g f hunit
    (BanachSpectrum.comap φ.toBoundedRingHom x) (himage x)

/-- The spectrum inequalities bound every power, hence every monomial,
of any fraction tuple satisfying the actual denominator equations. -/
theorem solutions_bounded
    (hunit : RationalLocalization.GeneratesUnitIdeal K P m g f)
    (himage : ∀ x : BanachSpectrum Q,
      BanachSpectrum.comap φ.toBoundedRingHom x ∈ RationalLocalization.locus K P m g f)
    (b : Fin m → Q) (heq : ∀ j, φ g * b j = φ (f j)) :
    HasBoundedMonomials (Fin m) Q b := by
  apply (hasBoundedMonomials_iff_pow_bound (Fin m) Q b).mpr
  intro j
  apply hasBoundedPowers_of_spectrum_le_one Q (b j)
  intro x
  have hg : 0 < x (φ g) := lt_of_le_of_ne (apply_nonneg x.toMulRingSeminorm (φ g))
    (Ne.symm (denominator_ne_zero K P m g f hunit
      (BanachSpectrum.comap φ.toBoundedRingHom x) (himage x)))
  have hj : x (φ g) * x (b j) ≤ x (φ g) := by
    rw [← map_mul x.toMulRingSeminorm, heq j]
    exact himage x j
  exact (mul_le_mul_iff_of_pos_left hg).mp (by simpa only [mul_one] using hj)

/-- Actual fractions and bounded quotient evaluation produce the unique extension. -/
theorem existsUnique_extension_of_image
    (hunit : RationalLocalization.GeneratesUnitIdeal K P m g f)
    (himage : ∀ x : BanachSpectrum Q,
      BanachSpectrum.comap φ.toBoundedRingHom x ∈ RationalLocalization.locus K P m g f) :
    ∃! ψ : BoundedAlgHom K (RationalLocalization.algebra K P m g f) Q,
      ψ.comp (RationalLocalization.baseMap K P m g f) = φ := by
  obtain ⟨a, ha⟩ := isUnit_image_denominator K P m g f Q φ hunit himage
  let b : Fin m → Q := fun j => (↑a⁻¹ : Q) * φ (f j)
  have heq (j : Fin m) : φ g * b j = φ (f j) := by
    rw [← ha]
    simp [b, ← mul_assoc]
  exact RationalLocalization.existsUnique_extension K P m g f Q hunit φ b
    (solutions_bounded K P m g f Q φ hunit himage b heq) heq

/-- Any bounded factorization pulls spectrum points back into the rational locus. -/
theorem image_of_extension
    (ψ : BoundedAlgHom K (RationalLocalization.algebra K P m g f) Q)
    (hψ : ψ.comp (RationalLocalization.baseMap K P m g f) = φ) :
    ∀ x : BanachSpectrum Q,
      BanachSpectrum.comap φ.toBoundedRingHom x ∈ RationalLocalization.locus K P m g f := by
  intro x j
  have h := RationalLocalization.comap_mem_locus K P m g f
    (BanachSpectrum.comap ψ.toBoundedRingHom x) j
  change x (ψ (RationalLocalization.baseMap K P m g f (f j))) ≤
    x (ψ (RationalLocalization.baseMap K P m g f g)) at h
  have hf := congrArg (fun χ => χ (f j)) hψ
  have hg := congrArg (fun χ => χ g) hψ
  change ψ (RationalLocalization.baseMap K P m g f (f j)) = φ (f j) at hf
  change ψ (RationalLocalization.baseMap K P m g f g) = φ g at hg
  change x (φ (f j)) ≤ x (φ g)
  simpa only [hf, hg] using h

/-- Spectrum-image containment characterizes unique bounded rational factorization
for every presented strict affinoid test algebra. -/
theorem factorization : FactorizationStatement.{u} := by
  intro K _ _ _ P m g f hunit Q φ
  constructor
  · exact existsUnique_extension_of_image K P m g f Q φ hunit
  · rintro ⟨ψ, hψ, _⟩
    exact image_of_extension K P m g f Q φ ψ hψ

/-- The same strict-test factorization follows from no common spectrum zeros,
without a supplied algebraic ideal equation. -/
theorem factorization_of_no_common_zero
    (hzero : ∀ x : BanachSpectrum P, x g ≠ 0 ∨ ∃ j, x (f j) ≠ 0) :
    (∀ x : BanachSpectrum Q,
      BanachSpectrum.comap φ.toBoundedRingHom x ∈ RationalLocalization.locus K P m g f) ↔
    ∃! ψ : BoundedAlgHom K (RationalLocalization.algebra K P m g f) Q,
      ψ.comp (RationalLocalization.baseMap K P m g f) = φ :=
  factorization K P m g f
    ((generatesUnitIdeal_iff_no_common_zero K P m g f).mpr hzero) Q φ

end Langlands.Analytic.RationalFactorization
