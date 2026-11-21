import Langlands.HarmonicAnalysis.Distribution.LocalProductChartDescent
import Langlands.HarmonicAnalysis.Distribution.SmoothDistributionLocality
import Langlands.LinearAlgebra.RealSpectralStratumChart
import Mathlib.Order.Preorder.Finite

/-! # Support descent by real matrix spectral labels -/

noncomputable section

open Filter Set TopologicalSpace
open scoped ContDiff Distributions Matrix.Norms.Operator Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.HarmonicAnalysis

variable {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/-- The matrices whose spectral label is strictly greater than that of `A`. -/
def realMatrixSpectralStrictSuperlevel (A : Mat) : Set Mat :=
  {B | realMatrixSpectralRankLabel A < realMatrixSpectralRankLabel B}

/-- Near a chart center, the real spectral label cannot decrease. If points
of the same label lie in the zero section, every nearby point off that
section has strictly higher label. -/
theorem eventually_realSpectralChart_off_zero {E W : Type*}
    [TopologicalSpace E] [TopologicalSpace W] [Zero W]
    {A : Mat} {x : E} (e : OpenPartialHomeomorph (E × W) Mat)
    (h₀ : (x, 0) ∈ e.source) (hA : e (x, 0) = A)
    (hfixed : ∀ᶠ B in 𝓝 A, realMatrixSpectralRankLabel B = realMatrixSpectralRankLabel A →
      B ∈ e.target ∧ (e.symm B).2 = 0) :
    ∀ᶠ p in 𝓝 (x, (0 : W)), p ∈ e.source ∧
      realMatrixSpectralRankLabel A ≤ realMatrixSpectralRankLabel (e p) ∧
      (p.2 ≠ 0 → realMatrixSpectralRankLabel A < realMatrixSpectralRankLabel (e p)) := by
  have hge : ∀ᶠ B in 𝓝 A, realMatrixSpectralRankLabel A ≤ realMatrixSpectralRankLabel B :=
    (continuous_realMatrixComplexification n).continuousAt.eventually
      (eventually_matrixSpectralRankLabel_ge (realMatrixComplexification n A))
  have hsource := e.open_source.mem_nhds h₀
  have he : Tendsto e (𝓝 (x, (0 : W))) (𝓝 A) :=
    hA ▸ e.continuousOn.continuousAt hsource
  filter_upwards [hsource, he.eventually hge, he.eventually hfixed] with p hp hle hf
  refine ⟨hp, hle, fun hne => lt_of_le_of_ne hle ?_⟩
  intro heq
  have hn := (hf heq.symm).2
  rw [e.left_inv hp] at hn
  exact hne hn

/-- A product neighborhood of the chart center can be chosen inside any
prescribed neighborhood, with its off-zero part mapping to higher labels. -/
theorem exists_realSpectralChart_product {E W : Type*}
    [TopologicalSpace E] [TopologicalSpace W] [Zero W]
    {A : Mat} {x : E} (e : OpenPartialHomeomorph (E × W) Mat)
    (h₀ : (x, 0) ∈ e.source) (hA : e (x, 0) = A)
    (hfixed : ∀ᶠ B in 𝓝 A, realMatrixSpectralRankLabel B = realMatrixSpectralRankLabel A →
      B ∈ e.target ∧ (e.symm B).2 = 0)
    {s : Set (E × W)} (hs : s ∈ 𝓝 (x, (0 : W))) :
    ∃ U : Opens E, ∃ V : Opens W,
      x ∈ U ∧ 0 ∈ V ∧ (U : Set E) ×ˢ (V : Set W) ⊆ s ∧
        (U : Set E) ×ˢ (V : Set W) ⊆ e.source ∧
        e '' ({p : E × W | p.2 ≠ 0} ∩ ((U : Set E) ×ˢ (V : Set W))) ⊆
          realMatrixSpectralStrictSuperlevel A := by
  have hnear : ∀ᶠ p in 𝓝 (x, (0 : W)),
      p ∈ s ∧ p ∈ e.source ∧
        (p.2 ≠ 0 → realMatrixSpectralRankLabel A < realMatrixSpectralRankLabel (e p)) := by
    filter_upwards [hs, eventually_realSpectralChart_off_zero e h₀ hA hfixed]
      with p hp hspec
    exact ⟨hp, hspec.1, hspec.2.2⟩
  obtain ⟨U, V, hU, hx, hV, hzero, hUV⟩ := mem_nhds_prod_iff'.mp hnear
  refine ⟨⟨U, hU⟩, ⟨V, hV⟩, hx, hzero, fun p hp => (hUV hp).1,
    fun p hp => (hUV hp).2.1, ?_⟩
  rintro _ ⟨p, ⟨hn, hp⟩, rfl⟩
  exact (hUV hp).2.2 hn

/-- The real spectral labels have only finitely many values at fixed size. -/
theorem finite_range_realMatrixSpectralRankLabel :
    (Set.range (realMatrixSpectralRankLabel (n := n))).Finite := by
  have hfinite := (Set.finite_le_nat n).prod (Set.finite_le_nat (n * ((n + 1) * n)))
  refine (hfinite.image toLex).subset ?_
  rintro _ ⟨A, rfl⟩
  exact ⟨ofLex (realMatrixSpectralRankLabel A), realMatrixSpectralRankLabel_bounds A, rfl⟩

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A zero chart restriction on a product around the center gives an open
ambient neighborhood on which the distribution vanishes. -/
theorem exists_vanishingNeighborhood_of_productChart_eq_zero {X E W : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {U : Opens E} {V : Opens W} {p : E × W}
    (e : OpenPartialHomeomorph (E × W) X)
    (he : ContDiffOn ℝ ∞ e e.source) (he' : ContDiffOn ℝ ∞ e.symm e.target)
    (hp : p ∈ productTestDomain U V) (hUV : productTestDomain U V ≤ chartSource e)
    (D : 𝓓'((⊤ : Opens X), F)) (hzero : restrictProductChartDistribution e he' hUV D = 0) :
    ∃ O : Opens X, e p ∈ O ∧ Distribution.IsVanishingOn D (O : Set X) := by
  let Ω := productTestDomain U V
  refine ⟨⟨e '' (Ω : Set (E × W)), e.isOpen_image_of_subset_source Ω.isOpen hUV⟩,
    ⟨p, hp, rfl⟩, ?_⟩
  exact isVanishingOn_chartImage_of_restrictProductChartDistribution_eq_zero e he' he hUV D hzero

/-- If vanishing at all strictly higher labels implies vanishing near each
point, the distribution is zero by taking a maximal label on its support. -/
theorem realMatrixDistribution_eq_zero_of_spectralDescent
    (D : 𝓓'((⊤ : Opens Mat), F))
    (hlocal : ∀ A : Mat,
      Distribution.IsVanishingOn D (realMatrixSpectralStrictSuperlevel A) →
      ∃ U : Opens Mat, A ∈ U ∧ Distribution.IsVanishingOn D (U : Set Mat)) : D = 0 := by
  apply smoothDistribution_eq_zero_of_dsupport_eq_empty D
  by_contra h
  have hfinite := finite_range_realMatrixSpectralRankLabel (n := n)
  have hlabels : (realMatrixSpectralRankLabel (n := n) '' Distribution.dsupport D).Finite :=
    hfinite.subset (Set.image_subset_range _ _)
  obtain ⟨A, hA, hmax⟩ := Set.Finite.exists_maximalFor' realMatrixSpectralRankLabel
    (Distribution.dsupport D) hlabels (Set.nonempty_iff_ne_empty.mpr h)
  have hgt : realMatrixSpectralStrictSuperlevel A ⊆
      (Distribution.dsupport D)ᶜ := by
    intro B hB hs
    exact (not_le_of_gt hB) (hmax hs (le_of_lt hB))
  obtain ⟨U, hU, hv⟩ := hlocal A
    (Distribution.IsVanishingOn.mono hgt (smoothDistribution_isVanishingOn_compl_dsupport D))
  exact (Distribution.notMem_dsupport_iff A).mpr ⟨U, hv, U.isOpen, hU⟩ hA

end Langlands.HarmonicAnalysis
