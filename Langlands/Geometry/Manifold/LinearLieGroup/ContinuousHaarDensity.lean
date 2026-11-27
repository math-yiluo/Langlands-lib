import Langlands.Geometry.Manifold.LinearLieGroup.HaarDensity
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.LocallyConvex.SeparatingDual

/-! # Continuous kernels in coordinates of the second kind

For `h : IsExpLieAlgebra G 𝔤`, a basis `b` of `𝔤` and a left Haar measure `μ` on `G`,
`IsExpLieAlgebra.exists_continuous_density_prodExp` gives `ε > 0` such that every continuous
kernel `K` on `ℝᵈ` supported in the closed ball `B̄(0, ε)` is carried by `P = h.prodExp b` to a
continuous compactly supported `κ` on `G`: `∫ κ φ dμ = ∫ K(t) φ(P t) dt` for continuous `φ`.
`IsExpLieAlgebra.exists_continuous_density_prodExp_smul` is the same identity for continuous
functions with values in a complex Banach space. The construction `κ = (K / ρ) ∘ c` is that of
`IsExpLieAlgebra.exists_smooth_density_prodExp`, with the Haar density `ρ` and the local inverse `c`
of `P` from `IsExpLieAlgebra.exists_haar_density_prodExp`. -/

namespace Langlands.LinearLieGroup

open scoped Manifold ContDiff Topology
open NormedSpace Set Filter MeasureTheory Metric

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸}

namespace IsExpLieAlgebra

variable (h : IsExpLieAlgebra G 𝔤)

/-- **Continuous kernels on `ℝᵈ` are pull-backs of continuous functions on `G`.** There is `ε > 0`
such that every continuous `K` on `ℝᵈ` supported in the closed ball `B̄(0, ε)` comes from a
continuous compactly supported `κ` on `G` with `∫ κ φ dμ = ∫ K(t) φ(P t) dt` for every continuous
`φ`, where `P = prodExp b`: take `κ = (K / ρ) ∘ c` on `W` with the data of
`exists_haar_density_prodExp`. -/
theorem exists_continuous_density_prodExp [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [μ.IsHaarMeasure] {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) :
    ∃ ε > 0, ∀ K : (Fin d → ℝ) → ℂ, Continuous K → tsupport K ⊆ closedBall 0 ε →
      ∃ κ : G → ℂ, Continuous κ ∧ HasCompactSupport κ ∧
        ∀ φ : G → ℂ, Continuous φ → ∫ y, κ y * φ y ∂μ = ∫ t, K t * φ (h.prodExp (⇑b) t) := by
  obtain ⟨r, ρ, c, W, hr, hρ, hρpos, hW, hPW, hcP, hc, hint⟩ := h.exists_haar_density_prodExp μ b
  set P := h.prodExp (⇑b) with hPdef
  have hPc : Continuous P := h.continuous_prodExp _
  refine ⟨r / 2, by positivity, fun K hK hKs => ?_⟩
  have hεr : closedBall (0 : Fin d → ℝ) (r / 2) ⊆ ball 0 r :=
    closedBall_subset_ball (by linarith)
  set C := P '' closedBall (0 : Fin d → ℝ) (r / 2) with hCdef
  have hCc : IsCompact C := (isCompact_closedBall _ _).image hPc
  let κ : G → ℂ := W.indicator fun y => K (c y) * (((ρ (c y))⁻¹ : ℝ) : ℂ)
  have hκC : ∀ y, y ∉ C → κ y = 0 := by
    intro y hy
    by_cases hyW : y ∈ W
    · have hz : c y ∉ closedBall (0 : Fin d → ℝ) (r / 2) := fun hz => hy ⟨c y, hz, hcP y hyW⟩
      have : K (c y) = 0 := image_eq_zero_of_notMem_tsupport fun h' => hz (hKs h')
      simp [κ, indicator_of_mem hyW, this]
    · simp [κ, indicator_of_notMem hyW]
  have hκsupp : tsupport κ ⊆ C :=
    closure_minimal (fun y hy => by_contra fun h' => hy (hκC y h')) hCc.isClosed
  have hκW : ∀ z ∈ ball (0 : Fin d → ℝ) r, κ (P z) * (ρ z : ℂ) = K z := by
    intro z hz
    obtain ⟨hzW, hcz⟩ := hPW z hz
    have hρz : (ρ z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hρpos z hz).ne'
    simp only [κ, indicator_of_mem hzW, hcz, Complex.ofReal_inv]
    field_simp
  have hcW : ∀ g ∈ W, ContinuousAt c g := by
    intro g hg
    have h1 : ContDiffAt ℝ 0 (fun Y : 𝔤 => c (g * h.expG Y)) 0 := (hc g hg).of_le (by simp)
    have h2 := (h.contMDiffAt_iff_expG (n := 0) (f := c) (g := g)).2 h1
    let := h.chartedSpace
    exact h2.continuousAt
  have hκc : Continuous κ := by
    rw [continuous_iff_continuousAt]
    intro g
    by_cases hg : g ∈ C
    · obtain ⟨z₀, hz₀, rfl⟩ := hg
      obtain ⟨hgW, hcg⟩ := hPW z₀ (hεr hz₀)
      have hev : (fun y => K (c y) * (((ρ (c y))⁻¹ : ℝ) : ℂ)) =ᶠ[𝓝 (P z₀)] κ := by
        filter_upwards [hW.mem_nhds hgW] with y hy
        simp [κ, indicator_of_mem hy]
      refine ContinuousAt.congr ?_ hev
      have hρ0 : ρ (c (P z₀)) ≠ 0 := by rw [hcg]; exact (hρpos z₀ (hεr hz₀)).ne'
      exact (hK.continuousAt.comp (hcW _ hgW)).mul
        (Complex.continuous_ofReal.continuousAt.comp
          ((hρ.continuous.continuousAt.comp (hcW _ hgW)).inv₀ hρ0))
    · have hev : (fun _ => (0 : ℂ)) =ᶠ[𝓝 g] κ := by
        filter_upwards [hCc.isClosed.isOpen_compl.mem_nhds hg] with y hy
        exact (hκC y hy).symm
      exact continuousAt_const.congr hev
  refine ⟨κ, hκc, HasCompactSupport.intro hCc hκC, fun φ hφ => ?_⟩
  have hψ₀s : tsupport (fun y => κ y * φ y) ⊆ P '' ball 0 r :=
    (tsupport_mul_subset_left).trans (hκsupp.trans (image_mono hεr))
  rw [hint (fun y => κ y * φ y) (hκc.mul hφ)
    ((HasCompactSupport.intro hCc hκC).mul_right) hψ₀s]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (f := fun t => K t * φ (P t))
    (s := ball (0 : Fin d → ℝ) r) fun z hz => by
      have : K z = 0 := image_eq_zero_of_notMem_tsupport fun h' => hz (hεr (hKs h'))
      simp [this]]
  refine setIntegral_congr_fun measurableSet_ball fun z hz => ?_
  rw [mul_right_comm, hκW z hz]

/-- The vector-valued form of `exists_continuous_density_prodExp`: for every continuous `f` with
values in a complex Banach space, `∫ κ f dμ = ∫ K(t) f(P t) dt`. It follows from the scalar form by
applying continuous linear functionals, which separate points (Hahn–Banach). -/
theorem exists_continuous_density_prodExp_smul.{u} [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] {d : ℕ} (b : Module.Basis (Fin d) ℝ 𝔤) :
    ∃ ε > 0, ∀ K : (Fin d → ℝ) → ℂ, Continuous K → tsupport K ⊆ closedBall 0 ε →
      ∃ κ : G → ℂ, Continuous κ ∧ HasCompactSupport κ ∧
        ∀ (V : Type u) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (f : G → V),
          Continuous f → ∫ y, κ y • f y ∂μ = ∫ t, K t • f (h.prodExp (⇑b) t) := by
  obtain ⟨ε, hε, hdens⟩ := h.exists_continuous_density_prodExp μ b
  refine ⟨ε, hε, fun K hK hKs => ?_⟩
  obtain ⟨κ, hκc, hκs, hκ⟩ := hdens K hK hKs
  refine ⟨κ, hκc, hκs, fun V _ _ _ f hf => ?_⟩
  have hKc : HasCompactSupport K :=
    (isCompact_closedBall 0 ε).of_isClosed_subset (isClosed_tsupport _) hKs
  have hi1 : Integrable (fun y => κ y • f y) μ :=
    (hκc.smul hf).integrable_of_hasCompactSupport hκs.smul_right
  have hi2 : Integrable (fun t => K t • f (h.prodExp (⇑b) t)) :=
    (hK.smul (hf.comp (h.continuous_prodExp _))).integrable_of_hasCompactSupport hKc.smul_right
  refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℂ)).2 fun ℓ => ?_
  rw [← ℓ.integral_comp_comm hi1, ← ℓ.integral_comp_comm hi2]
  simp only [map_smul, smul_eq_mul]
  exact hκ (fun y => ℓ (f y)) (ℓ.continuous.comp hf)

end IsExpLieAlgebra

end Langlands.LinearLieGroup
