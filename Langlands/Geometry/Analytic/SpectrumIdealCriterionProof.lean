import Langlands.Geometry.Analytic.SpectrumIdealCriterionStatement
import Langlands.Geometry.Analytic.SpectrumNonemptyProof
import Langlands.Geometry.Analytic.Spectrum.Quotient

/-! # Spectrum detection of proper ideals and units of strict affinoids -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedStrictAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

/-- With trivial scalar norms, a maximal ideal above the given proper ideal
supplies a point, without assuming closedness or a norm on the prime quotient. -/
theorem exists_spectrum_kernel_of_proper_ideal_of_scalar_norm_le_one
    (P : PresentedStrictAffinoidAlgebra K) (hK : ∀ c : K, ‖c‖ ≤ 1)
    (I : Ideal P) (hI : I ≠ ⊤) : ∃ x : BanachSpectrum P, I ≤ x.kernel := by
  classical
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hI
  let _ : M.IsMaximal := hM
  refine ⟨primePoint_of_scalar_norm_le_one P hK M, ?_⟩
  intro a ha
  change (1 : MulRingSeminorm (P ⧸ M)) (Ideal.Quotient.mk M a) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hIM ha), map_zero]

variable [CompleteSpace K]

/-- A proper ideal is annihilated by an actual bounded spectrum point.
The nontrivial-valuation branch constructs a new closed-ideal Tate presentation. -/
theorem exists_spectrum_kernel_of_proper_ideal
    (P : PresentedStrictAffinoidAlgebra K) (I : Ideal P) (hI : I ≠ ⊤) :
    ∃ x : BanachSpectrum P, I ≤ x.kernel := by
  by_cases hK : ∀ c : K, ‖c‖ ≤ 1
  · exact exists_spectrum_kernel_of_proper_ideal_of_scalar_norm_le_one P hK I hI
  push Not at hK
  let _ : NontriviallyNormedField K :=
    { toNormedField := inferInstance, non_trivial := hK }
  let J := I.comap (presentationMap K P).toAlgHom.toRingHom
  have hJ : J ≠ ⊤ := Ideal.comap_ne_top _ hI
  let Q : PresentedStrictAffinoidAlgebra K :=
    { arity := P.arity
      ideal := J
      ideal_closed := isClosed_ideal_of_noetherian_banach (K := K) J }
  let _ : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr hJ
  obtain ⟨y⟩ := spectrum_nonempty Q
  let z := BanachSpectrum.comap (presentationMap K Q).toBoundedRingHom y
  have hz (f : StrictTateAlgebra (Fin P.arity) K) (hf : f ∈ J) : z f = 0 := by
    change y.toMulRingSeminorm (Ideal.Quotient.mk J f) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hf]
    change y.toMulRingSeminorm (0 : Q) = 0
    exact map_zero y.toMulRingSeminorm
  have hPJ : P.ideal ≤ J := by
    intro f hf
    change Ideal.Quotient.mk P.ideal f ∈ I
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hf]
    exact I.zero_mem
  let _ : IsClosed (P.ideal : Set (StrictTateAlgebra (Fin P.arity) K)) := P.ideal_closed
  have hPz : P.ideal ≤ z.kernel := fun f hf => hz f (hPJ hf)
  let x : BanachSpectrum P := BanachSpectrum.descend P.ideal z hPz
  refine ⟨x, ?_⟩
  intro a ha
  obtain ⟨f, rfl⟩ := presentationMap_surjective K P a
  change z f = 0
  exact hz f ha

/-- Units are exactly the elements annihilated by no bounded spectrum point. -/
theorem isUnit_iff_forall_spectrum_ne_zero
    (P : PresentedStrictAffinoidAlgebra K) (a : P) :
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
    (P : PresentedStrictAffinoidAlgebra K) (m : ℕ) (f : Fin m → P) :
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

/-- The entire published conjunction of proper-ideal and unit criteria. -/
theorem spectrumIdealCriterion : SpectrumIdealCriterionStatement K :=
  ⟨exists_spectrum_kernel_of_proper_ideal, isUnit_iff_forall_spectrum_ne_zero,
    span_range_eq_top_iff_forall_spectrum_exists_ne_zero⟩

end Langlands.Analytic.PresentedStrictAffinoidAlgebra
