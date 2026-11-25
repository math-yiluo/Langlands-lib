import Langlands.Analysis.DixmierMalliavin.LinearGroup
import Langlands.Geometry.Manifold.LinearLieGroup.Realization
import Langlands.Representation.Archimedean.GardingKernelOperations

/-!
# The Dixmier–Malliavin theorem for Lie groups with a closed linear realization

For a Lie group `G` modelled on a real normed space `E`, with a closed linear realization
`ρ : G →* 𝔸ˣ` (`Langlands.LinearLieGroup.IsClosedLinearRealization`) and a left Haar measure `μ`:

* `Langlands.Archimedean.exists_eq_sum_gardingKernelConvolution`: every `f` in
  `smoothCompactKernels E G` is `∑ᵢ gardingKernelConvolution μ (φ i) (ψ i)` for finitely many
  `φ i`, `ψ i` in `smoothCompactKernels E G`, with `tsupport (φ i)` in a prescribed neighbourhood of
  `1` and `tsupport (ψ i) ⊆ tsupport f`;
* `Langlands.Archimedean.exists_eq_sum_gardingKernelConvolution_units`: the case `G = 𝔸ˣ`, `ρ = id`.

The proof transports `f` to the image of `ρ`, a closed subgroup of `𝔸ˣ` with exponential charts
(`IsClosedLinearRealization.contMDiff_iff_comp_symm`), applies the theorem on linear groups
(`IsExpLieAlgebra.exists_eq_sum_convolutionIntegral`) with the image of `μ`, and transports back
with `Langlands.Hecke.convolutionIntegral_comp_continuousMulEquiv`.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped Manifold ContDiff

namespace Langlands.Hecke

/-- Convolution is transported by an isomorphism of topological groups:
`(f ∘ e) ⋆_μ (g ∘ e) = (f ⋆_{e_* μ} g) ∘ e`. -/
theorem convolutionIntegral_comp_continuousMulEquiv {G G' : Type*} [Group G] [TopologicalSpace G]
    [MeasurableSpace G] [BorelSpace G] [Group G'] [TopologicalSpace G'] [MeasurableSpace G']
    [BorelSpace G'] (e : G ≃ₜ* G') (μ : Measure G) (f g : G' → ℂ) (x : G) :
    convolutionIntegral μ (f ∘ e) (g ∘ e) x = convolutionIntegral (μ.map e) f g (e x) := by
  rw [convolutionIntegral, convolutionIntegral]
  have h := integral_map_equiv (μ := μ) e.toHomeomorph.toMeasurableEquiv
    (fun z => f z * g (z⁻¹ * e x))
  change _ = ∫ y, f y * g (y⁻¹ * e x) ∂Measure.map ⇑(e.toHomeomorph.toMeasurableEquiv) μ
  rw [h]
  congr 1
  funext y
  simp only [Function.comp_apply, map_mul, map_inv]
  rfl

end Langlands.Hecke

namespace Langlands.Archimedean

open LinearLieGroup

/-- **Dixmier–Malliavin** for a Lie group with a closed linear realization: every smooth compactly
supported function `f` on `G` is a finite sum `∑ φᵢ ⋆ ψᵢ` of convolutions of smooth compactly
supported functions, with `φᵢ` supported in a prescribed neighbourhood `U` of `1` and `ψᵢ` supported in
the support of `f`. The convolution is `gardingKernelConvolution μ` for a left Haar measure `μ`. -/
theorem exists_eq_sum_gardingKernelConvolution
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [ChartedSpace E G] [LieGroup 𝓘(ℝ, E) ∞ G] [T2Space G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
    {ρ : G →* 𝔸ˣ} (hρ : LinearLieGroup.IsClosedLinearRealization 𝓘(ℝ, E) ρ)
    (μ : Measure G) [μ.IsHaarMeasure] {U : Set G} (hU : U ∈ 𝓝 1)
    (f : smoothCompactKernels E G) :
    ∃ (n : ℕ) (φ ψ : Fin n → smoothCompactKernels E G),
      (∀ i, tsupport (φ i).val ⊆ U ∧ tsupport (ψ i).val ⊆ tsupport f.val) ∧
      f = ∑ i, gardingKernelConvolution μ (φ i) (ψ i) := by
  set K := ρ.range
  set hK := hρ.isExpLieAlgebra
  set e : G ≃ₜ* K := hρ.rangeEquiv
  let : MeasurableSpace K := borel K
  have : BorelSpace K := ⟨rfl⟩
  have : (μ.map e).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map μ e
  have hsmooth := hρ.contMDiff_iff_comp_symm (F := ℂ)
  set f' : K → ℂ := f.val ∘ e.symm
  have hf' := (hsmooth f.val).1 f.property.1
  have hf'c : HasCompactSupport f' := f.property.2.comp_homeomorph e.symm.toHomeomorph
  have hU' : e.symm ⁻¹' U ∈ 𝓝 (1 : K) :=
    (e.symm.continuous.continuousAt (x := 1)).preimage_mem_nhds (by simpa using hU)
  obtain ⟨n, φ', ψ', hφψ, hsum⟩ := hK.exists_eq_sum_convolutionIntegral (μ.map e) hU' f' hf' hf'c
  have hcomp : ∀ u : K → ℂ, (letI := hK.chartedSpace;
      ContMDiff 𝓘(ℝ, lieSubmodule ρ.range hρ.isClosed_range) 𝓘(ℝ, ℂ) ∞ u) →
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ (u ∘ e) := by
    intro u hu
    refine (hsmooth (u ∘ e)).2 ?_
    have : (u ∘ e) ∘ e.symm = u := by funext k; simp
    rwa [this]
  have htsupp : ∀ u : K → ℂ, tsupport (u ∘ e) = e ⁻¹' tsupport u := fun u =>
    tsupport_comp_eq_preimage u e.toHomeomorph
  have htf : tsupport f' = e.symm ⁻¹' tsupport f.val :=
    tsupport_comp_eq_preimage f.val e.symm.toHomeomorph
  let φ : Fin n → smoothCompactKernels E G := fun i =>
    ⟨φ' i ∘ e, hcomp _ (hφψ i).1, (hφψ i).2.1.comp_homeomorph e.toHomeomorph⟩
  let ψ : Fin n → smoothCompactKernels E G := fun i =>
    ⟨ψ' i ∘ e, hcomp _ (hφψ i).2.2.2.1,
      (show HasCompactSupport (ψ' i) from
        hf'c.of_isClosed_subset (isClosed_tsupport _) (hφψ i).2.2.2.2).comp_homeomorph
        e.toHomeomorph⟩
  refine ⟨n, φ, ψ, fun i => ⟨?_, ?_⟩, ?_⟩
  · change tsupport (φ' i ∘ e) ⊆ U
    rw [htsupp]
    intro x hx
    have := (hφψ i).2.2.1 hx
    simpa using this
  · change tsupport (ψ' i ∘ e) ⊆ tsupport f.val
    rw [htsupp]
    intro x hx
    have := (hφψ i).2.2.2.2 hx
    rw [htf] at this
    simpa using this
  · apply Subtype.ext
    funext x
    rw [Submodule.coe_sum, Finset.sum_apply]
    have hx : f.val x = f' (e x) := by simp [f']
    rw [hx, hsum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [gardingKernelConvolution_apply, ← Hecke.convolutionIntegral_comp_continuousMulEquiv]
    rfl

/-- **Dixmier–Malliavin for `𝔸ˣ`** (`GL_n(ℝ)`, `GL_n(ℂ)`, the units of a finite-dimensional real algebra),
with Mathlib's manifold structure on the units. -/
theorem exists_eq_sum_gardingKernelConvolution_units
    {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
    [MeasurableSpace 𝔸ˣ] [BorelSpace 𝔸ˣ] (μ : Measure 𝔸ˣ) [μ.IsHaarMeasure]
    {U : Set 𝔸ˣ} (hU : U ∈ 𝓝 1) (f : smoothCompactKernels 𝔸 𝔸ˣ) :
    ∃ (n : ℕ) (φ ψ : Fin n → smoothCompactKernels 𝔸 𝔸ˣ),
      (∀ i, tsupport (φ i).val ⊆ U ∧ tsupport (ψ i).val ⊆ tsupport f.val) ∧
      f = ∑ i, gardingKernelConvolution μ (φ i) (ψ i) :=
  exists_eq_sum_gardingKernelConvolution isClosedLinearRealization_id μ hU f

end Langlands.Archimedean
