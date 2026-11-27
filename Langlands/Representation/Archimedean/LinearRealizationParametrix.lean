import Langlands.Representation.Archimedean.OneParameterParametrix
import Langlands.Geometry.Manifold.LinearLieGroup.ContinuousHaarDensity
import Langlands.Geometry.Manifold.LinearLieGroup.Realization

/-! # A local Sobolev identity on Lie groups with a closed linear realization

`Langlands.Archimedean.exists_sum_integral_iteratedLieDerivative`: on a Lie group `G` with a
closed linear realization and a left Haar measure `μ` there are finitely many words `wordⱼ` and
continuous compactly supported `κⱼ : G → ℂ` such that every smooth vector `w` of every strongly
continuous representation `π` of `G` on a complex Banach space is
`∑ⱼ ∫ κⱼ(g) π(g) dπ(wordⱼ) w dμ(g)`. -/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped Manifold ContDiff

namespace Langlands.Archimedean

open LinearLieGroup OneParameterParametrix

universe uE uG uV

/-- **A local Sobolev identity for smooth vectors.** Let `G` be a Lie group modelled on `E` with a
closed linear realization `ρ` and a left Haar measure `μ`. There are finitely many words `wordⱼ` in
`E` and continuous compactly supported `κⱼ : G → ℂ` such that every smooth vector `w` of every
strongly continuous representation `π` of `G` on a complex Banach space satisfies
`w = ∑ⱼ ∫ κⱼ(g) π(g) dπ(wordⱼ) w dμ(g)`. The words and functions do not depend on `π`.

The words are built from the tangent vectors at `0` of the one-parameter subgroups
`s ↦ ρ⁻¹(exp (s bᵢ))` for a basis `b` of the Lie algebra of the image of `ρ`
(`exists_sum_integral_curveProd`); the kernels on `ℝⁿ` become functions on `G` through the Haar
density in coordinates of the second kind (`exists_continuous_density_prodExp_smul`). -/
theorem exists_sum_integral_iteratedLieDerivative
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [ChartedSpace E G]
    [LieGroup 𝓘(ℝ, E) ∞ G] [MeasurableSpace G] [BorelSpace G]
    {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
    {ρ : G →* 𝔸ˣ} (hρ : IsClosedLinearRealization 𝓘(ℝ, E) ρ)
    (μ : Measure G) [μ.IsHaarMeasure] :
    ∃ (N : ℕ) (word : Fin N → List E) (κ : Fin N → G → ℂ),
      (∀ j, Continuous (κ j) ∧ HasCompactSupport (κ j)) ∧
      ∀ (V : Type uV) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
        (π : G →* (V →L[ℂ] V)), (∀ v, Continuous fun g => π g v) →
        ∀ w, IsSmoothVector 𝓘(ℝ, E) π w →
          w = ∑ j, ∫ g, κ j g • π g (iteratedLieDerivative 𝓘(ℝ, E) π (word j) w) ∂μ := by
  set H := ρ.range
  set hK := hρ.isExpLieAlgebra
  set e : G ≃ₜ* H := hρ.rangeEquiv
  let : MeasurableSpace H := borel H
  have : BorelSpace H := ⟨rfl⟩
  have : (μ.map e).IsHaarMeasure := ContinuousMulEquiv.isHaarMeasure_map μ e
  set 𝔥 := lieSubmodule ρ.range hρ.isClosed_range
  set n := Module.finrank ℝ 𝔥
  let b : Module.Basis (Fin n) ℝ 𝔥 := Module.finBasis ℝ 𝔥
  obtain ⟨ε, hε, hdens⟩ := hK.exists_continuous_density_prodExp_smul.{_, uV} (μ.map e) b
  let γ : Fin n → ℝ → G := fun i s => e.symm (hK.expG (s • b i))
  have hγ : ∀ i, ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (γ i) := by
    intro i
    let := hK.chartedSpace
    exact (hρ.contMDiff_rangeRestrict_and_symm).2.comp
      (hK.contMDiff_expG_comp (φ := fun s : ℝ => s • b i) (contDiff_id.smul contDiff_const))
  have hγm : ∀ i s t, γ i (s + t) = γ i s * γ i t := by
    intro i s t
    simp only [γ, hK.expG_add_smul, map_mul]
  obtain ⟨N, word, K, hK', hid⟩ := exists_sum_integral_curveProd.{uE, uG, uV} hε γ hγ hγm
  choose κ' hκ'c hκ's hκ' using fun j => hdens (K j) (hK' j).1 (hK' j).2
  refine ⟨N, word, fun j => κ' j ∘ e, fun j => ⟨(hκ'c j).comp e.continuous,
    (hκ's j).comp_homeomorph e.toHomeomorph⟩, fun V _ _ _ π hπ w hw => ?_⟩
  have hΓ : ∀ t, curveProd γ t = e.symm (hK.prodExp (⇑b) t) := by
    intro t
    simp only [curveProd, IsExpLieAlgebra.prodExp, γ, map_list_prod, List.map_ofFn,
      Function.comp_def]
  conv_lhs => rw [hid V π hπ w hw]
  refine Finset.sum_congr rfl fun j _ => ?_
  set u := iteratedLieDerivative 𝓘(ℝ, E) π (word j) w
  have hf : Continuous fun y : H => π (e.symm y) u := (hπ u).comp e.symm.continuous
  have h1 := hκ' j V (fun y : H => π (e.symm y) u) hf
  have h2 := integral_map_equiv (μ := μ) e.toHomeomorph.toMeasurableEquiv
    (fun y : H => κ' j y • π (e.symm y) u)
  have h3 : Measure.map ⇑(e.toHomeomorph.toMeasurableEquiv) μ = μ.map e := rfl
  rw [h3, h1] at h2
  simp_rw [hΓ]
  rw [h2]
  congr 1
  funext g
  simp only [Function.comp_apply]
  have : e.symm (e.toHomeomorph.toMeasurableEquiv g) = g := e.symm_apply_apply g
  rw [this]
  rfl

end Langlands.Archimedean
