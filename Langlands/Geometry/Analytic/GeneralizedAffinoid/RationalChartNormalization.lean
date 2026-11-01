import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartCategory
import Langlands.Geometry.Analytic.StrictTestDomain.Definitions

/-! # Normalizing rational inequalities after a change of coefficient field -/

noncomputable section

universe u v w

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {A : PresentedAffinoidAlgebra K}
  {L : Type w} [NormedField L] [IsUltrametricDist L]
  (d : RationalChart K A) (Q : PresentedStrictAffinoidAlgebra L)
  (ψ : BoundedRingHom A Q) (τ : Fin d.arity → L)
  (hτ : ∀ j, ‖τ j‖ = d.radii j)

/-- The actual strict rational data obtained by dividing each image numerator
by a scalar whose norm is its original relative radius. -/
def normalizedStrict : StrictTestDomain.RationalData L Q where
  arity := d.arity
  denominator := ψ (presentationMap K A d.denominator)
  numerator j := algebraMap L Q (τ j)⁻¹ * ψ (presentationMap K A (d.numerators j))
  no_common_zero x := by
    by_contra h
    push Not at h
    let y := BanachSpectrum.comap ψ x
    have hnum (j : Fin d.arity) : y (presentationMap K A (d.numerators j)) = 0 := by
      have hj := h.2 j
      change x.toMulRingSeminorm
        (algebraMap L Q (τ j)⁻¹ * ψ (presentationMap K A (d.numerators j))) = 0 at hj
      rw [map_mul, BanachSpectrum.algebraMap_apply, norm_inv, hτ] at hj
      exact (mul_eq_zero.mp hj).resolve_left (inv_ne_zero (d.radii.positive j).ne')
    have hle : Ideal.span (insert (presentationMap K A d.denominator)
        (Set.range fun j => presentationMap K A (d.numerators j))) ≤ y.kernel := by
      apply Ideal.span_le.mpr
      rintro a (rfl | ⟨j, rfl⟩)
      · exact h.1
      · exact hnum j
    rw [d.generates] at hle
    exact y.kernel_isPrime.ne_top (top_unique hle)

@[simp] theorem normalizedStrict_arity :
    (d.normalizedStrict Q ψ τ hτ).arity = d.arity := rfl

@[simp] theorem normalizedStrict_denominator :
    (d.normalizedStrict Q ψ τ hτ).denominator =
      ψ (presentationMap K A d.denominator) := rfl

@[simp] theorem normalizedStrict_numerator (j : Fin d.arity) :
    (d.normalizedStrict Q ψ τ hτ).numerator j =
      algebraMap L Q (τ j)⁻¹ * ψ (presentationMap K A (d.numerators j)) := rfl

/-- Normalizing the coefficients changes the written inequalities to unit
radii and preserves exactly the inverse image of the original locus. -/
theorem mem_normalizedStrict_locus_iff (x : BanachSpectrum Q) :
    x ∈ (d.normalizedStrict Q ψ τ hτ).locus ↔
      BanachSpectrum.comap ψ x ∈ d.locus := by
  change (∀ j, x (algebraMap L Q (τ j)⁻¹ *
    ψ (presentationMap K A (d.numerators j))) ≤
      x (ψ (presentationMap K A d.denominator))) ↔
    ∀ j, x (ψ (presentationMap K A (d.numerators j))) ≤
      d.radii j * x (ψ (presentationMap K A d.denominator))
  simp only [map_mul, BanachSpectrum.algebraMap_apply, norm_inv, hτ]
  exact forall_congr' fun j => inv_mul_le_iff₀ (d.radii.positive j)

theorem normalizedStrict_locus :
    (d.normalizedStrict Q ψ τ hτ).locus = BanachSpectrum.comap ψ ⁻¹' d.locus := by
  ext x
  exact d.mem_normalizedStrict_locus_iff Q ψ τ hτ x

variable {I : Type v}

/-- Every cover pulls back to a cover of the normalized strict chart loci.
Neither surjectivity of the coefficient map nor nonempty index sets are needed. -/
theorem normalizedStrict_cover
    (D : I → RationalChart K A)
    (τ : ∀ i, Fin (D i).arity → L)
    (hτ : ∀ i j, ‖τ i j‖ = (D i).radii j)
    (hcover : ∀ x : BanachSpectrum A, ∃ i, x ∈ (D i).locus) :
    ∀ x : BanachSpectrum Q,
      ∃ i, x ∈ ((D i).normalizedStrict Q ψ (τ i) (hτ i)).locus := by
  intro x
  obtain ⟨i, hi⟩ := hcover (BanachSpectrum.comap ψ x)
  exact ⟨i, ((D i).mem_normalizedStrict_locus_iff Q ψ (τ i) (hτ i) x).mpr hi⟩

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart
