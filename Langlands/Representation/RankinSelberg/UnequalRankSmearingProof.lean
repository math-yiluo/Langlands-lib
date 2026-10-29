import Langlands.Representation.RankinSelberg.UnequalRankSmearingAverage
import Langlands.HarmonicAnalysis.RowFourier
import Langlands.Representation.Hecke.TestFunction
import Mathlib.Topology.Separation.Profinite
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Small normalized cutoffs and a generic conditional Fourier-cutoff reduction. -/

noncomputable section

namespace Langlands.RankinSelberg.Smearing

open MeasureTheory HarmonicAnalysis Whittaker

universe uX uG uV

variable {X : Type uX} [TopologicalSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X]
variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

section SmallCutoff

variable [LocallyCompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]

/-- Every neighborhood admits a Schwartz function of integral one, supported
inside it, for the actual supplied measure. -/
theorem exists_normalized_schwartz_in_open (μ : Measure X)
    [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]
    (S : Set X) (hS : IsOpen S) (x₀ : X) (hx₀ : x₀ ∈ S) :
    ∃ Φ : SchwartzBruhat X, (∫ x, Φ x ∂μ) = 1 ∧
      ∀ x, Φ x ≠ 0 → x ∈ S := by
  obtain ⟨C, hC, hxC, hCS⟩ := exists_compact_subset hS hx₀
  obtain ⟨D, hD, hxD, hDC⟩ :=
    loc_compact_Haus_tot_disc_of_zero_dim.mem_nhds_iff.mp
      (isOpen_interior.mem_nhds hxC)
  have hDc : IsCompact D := hC.of_isClosed_subset hD.isClosed
    (hDC.trans interior_subset)
  have hm : (μ.real D : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (ne_of_gt (ENNReal.toReal_pos (ne_of_gt (hD.isOpen.measure_pos μ ⟨x₀, hxD⟩))
      hDc.measure_ne_top))
  let Φ : SchwartzBruhat X :=
    (μ.real D : ℂ)⁻¹ • Hecke.TestFunction.characteristic hD hDc
  refine ⟨Φ, ?_, ?_⟩
  · change (∫ x, (μ.real D : ℂ)⁻¹ * D.indicator (fun _ => (1 : ℂ)) x ∂μ) = 1
    rw [integral_const_mul, integral_indicator_const 1 hD.isOpen.measurableSet]
    simpa only [Complex.real_smul, mul_one] using inv_mul_cancel₀ hm
  · intro x hx
    have hxD' : x ∈ D := by
      by_contra hn
      apply hx
      simp [Φ, Hecke.TestFunction.characteristic_apply, hn]
    exact hCS (interior_subset (hDC hxD'))

omit [IsTopologicalGroup G] in
/-- A normalized small cutoff is supported on right translations fixing the
given coefficient, uniformly at every group element. -/
theorem exists_normalized_coefficient_cutoff (μ : Measure X)
    [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    {N : Subgroup G} {θ : N →* ℂˣ} (ℓ : functionals N θ ρ)
    (U : X → G) (hU : Continuous U) (x₀ : X) (hU₀ : U x₀ = 1)
    (f : (coefficientModel ρ ℓ).toSubmodule) :
    ∃ Φ : SchwartzBruhat X, (∫ x, Φ x ∂μ) = 1 ∧
      ∀ x, Φ x ≠ 0 → ∀ g, f.val.val (g * U x) = f.val.val g := by
  obtain ⟨K, hK⟩ := model_isSmooth ρ hρ ℓ f
  obtain ⟨Φ, hΦ, hΦS⟩ := exists_normalized_schwartz_in_open μ
    (U ⁻¹' (K : Set G)) (K.isOpen.preimage hU) x₀ (by simp [hU₀])
  refine ⟨Φ, hΦ, ?_⟩
  intro x hx g
  have he := congrArg (fun w : (coefficientModel ρ ℓ).toSubmodule => w.val.val g)
    (hK ⟨U x, hΦS x hx⟩)
  exact he

end SmallCutoff

section FourierCutoff

universe uF uI

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [MeasurableSpace F] [BorelSpace F]
variable {d : ℕ} [BorelSpace (Fin d → F)] {I : Type uI}

omit [IsTopologicalRing F] [BorelSpace F] in
/-- A supplied genuine Fourier pair turns the translation character identity
into a pointwise cutoff, retaining the global formula for the same coefficient. -/
theorem exists_coefficient_cutoff
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    [SigmaFinite ν.measure]
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    {N : Subgroup G} {θ : N →* ℂˣ} (ℓ : functionals N θ ρ)
    (U : (Fin d → F) → G) (hU : Continuous U)
    (κ Φ : SchwartzBruhat (Fin d → F)) (hpair : IsRowFourierPair ψ ν κ Φ)
    (f : (coefficientModel ρ ℓ).toSubmodule)
    (B : I → G) (x : I → Fin d → F)
    (hf : ∀ i z, f.val.val (B i * U z) =
      ψ.complex (rowPairing z (x i)) * f.val.val (B i)) :
    ∃ f₁ : (coefficientModel ρ ℓ).toSubmodule,
      (∀ h : G,
        Integrable (fun z => κ z * f.val.val (h * U z)) (rowMeasure ν d) ∧
        f₁.val.val h = ∫ z, κ z * f.val.val (h * U z) ∂rowMeasure ν d) ∧
      ∀ i, f₁.val.val (B i) = Φ (x i) * f.val.val (B i) := by
  obtain ⟨f₁, hglobal⟩ := exists_coefficient_average (rowMeasure ν d) ρ hρ ℓ U hU κ f
  refine ⟨f₁, hglobal, ?_⟩
  intro i
  rw [(hglobal (B i)).2]
  calc
    (∫ z, κ z * f.val.val (B i * U z) ∂rowMeasure ν d) =
        ∫ z, (ψ.complex (rowPairing z (x i)) * κ z) * f.val.val (B i)
          ∂rowMeasure ν d := by
      apply integral_congr_ae
      filter_upwards [] with z
      rw [hf i z]
      ring
    _ = rowFourierIntegral ψ ν d κ (x i) * f.val.val (B i) :=
      integral_mul_const _ _
    _ = Φ (x i) * f.val.val (B i) := by rw [← hpair (x i)]

end FourierCutoff

end Langlands.RankinSelberg.Smearing
