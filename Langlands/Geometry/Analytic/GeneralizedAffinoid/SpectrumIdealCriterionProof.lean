import Langlands.Geometry.Analytic.GeneralizedAffinoid.SpectrumIdealCriterionStatement
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RadiusRealization
import Langlands.Geometry.Analytic.GeneralizedAffinoid.StrictBaseChangeRetraction
import Langlands.Geometry.Analytic.SpectrumIdealCriterionProof

/-! # Spectrum detection of proper ideals and units at arbitrary positive radii -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- A proper ideal is annihilated by an actual bounded spectrum point. Its image in
the strict base change over a radius-realizing extension field stays proper, and a
point annihilating that image pulls back along the contractive base-change map. -/
theorem exists_spectrum_kernel_of_proper_ideal
    (P : PresentedAffinoidAlgebra K) (I : Ideal P) (hI : I ≠ ⊤) :
    ∃ x : BanachSpectrum P, I ≤ x.kernel := by
  obtain ⟨R⟩ := RadiusRealization.nonempty (K := K) P.arity P.polyradius
    P.polyradius.positive
  let Q := strictBaseChange P R.ι R.norm_ι R.norm_c
  let ψ : P →+* Q := strictBaseChangeHom P R.ι R.norm_ι R.norm_c
  have hJ : Ideal.map ψ I ≠ ⊤ :=
    map_strictBaseChangeHom_ne_top P R.ι R.norm_ι R.norm_c R.π R.π_ι_mul R.bound_pos.le
      R.norm_π_le R.π_one hI
  obtain ⟨y, hy⟩ :=
    PresentedStrictAffinoidAlgebra.exists_spectrum_kernel_of_proper_ideal Q _ hJ
  let ψb : BoundedRingHom P Q :=
    ⟨ψ, ⟨1, zero_lt_one, fun a => by
      rw [one_mul]
      exact norm_strictBaseChangeHom_le P R.ι R.norm_ι R.norm_c a⟩⟩
  exact ⟨BanachSpectrum.comap ψb y, fun a ha => hy (Ideal.mem_map_of_mem ψ ha)⟩

/-- Units are exactly the elements annihilated by no bounded spectrum point. -/
theorem isUnit_iff_forall_spectrum_ne_zero (P : PresentedAffinoidAlgebra K) (a : P) :
    IsUnit a ↔ ∀ x : BanachSpectrum P, x a ≠ 0 := by
  constructor
  · intro ha x hx
    have hle : Ideal.span ({a} : Set P) ≤ x.kernel := by
      apply Ideal.span_le.mpr
      intro b hb
      obtain rfl := Set.mem_singleton_iff.mp hb
      exact hx
    rw [Ideal.span_singleton_eq_top.mpr ha] at hle
    exact x.kernel_isPrime.ne_top (top_unique hle)
  · intro ha
    by_contra h
    have hI : Ideal.span ({a} : Set P) ≠ ⊤ :=
      fun hI => h (Ideal.span_singleton_eq_top.mp hI)
    obtain ⟨x, hx⟩ := exists_spectrum_kernel_of_proper_ideal P _ hI
    exact ha x (hx (Ideal.subset_span (Set.mem_singleton a)))

/-- A finite family generates the unit ideal exactly when it has no common
zero in the bounded spectrum, also for an empty family or the zero algebra. -/
theorem span_range_eq_top_iff_forall_spectrum_exists_ne_zero
    (P : PresentedAffinoidAlgebra K) (m : ℕ) (f : Fin m → P) :
    Ideal.span (Set.range f) = ⊤ ↔ ∀ x : BanachSpectrum P, ∃ i, x (f i) ≠ 0 := by
  constructor
  · intro h x
    by_contra hx
    push Not at hx
    have hle : Ideal.span (Set.range f) ≤ x.kernel := by
      apply Ideal.span_le.mpr
      rintro a ⟨i, rfl⟩
      exact hx i
    rw [h] at hle
    exact x.kernel_isPrime.ne_top (top_unique hle)
  · intro h
    by_contra hI
    obtain ⟨x, hx⟩ := exists_spectrum_kernel_of_proper_ideal P _ hI
    obtain ⟨i, hi⟩ := h x
    exact hi (hx (Ideal.subset_span ⟨i, rfl⟩))

variable (K) in
/-- The entire published conjunction of proper-ideal and unit criteria for
presentations with arbitrary positive radii. -/
theorem spectrumIdealCriterion : SpectrumIdealCriterionStatement K :=
  ⟨exists_spectrum_kernel_of_proper_ideal, isUnit_iff_forall_spectrum_ne_zero,
    span_range_eq_top_iff_forall_spectrum_exists_ne_zero⟩

end Langlands.Analytic.PresentedAffinoidAlgebra
