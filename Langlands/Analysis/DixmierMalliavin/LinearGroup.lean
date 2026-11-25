import Langlands.Analysis.ConvolutionIntegral
import Langlands.Analysis.DixmierMalliavin.DirectionalSeries
import Langlands.Analysis.DixmierMalliavin.IteratedKernel
import Langlands.Analysis.DixmierMalliavin.Line
import Langlands.Geometry.Manifold.LinearLieGroup.HaarDensity
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal

/-!
# The Dixmier–Malliavin theorem on linear Lie groups

For `h : IsExpLieAlgebra G 𝔤` (a Lie subgroup `G` of the units of a finite-dimensional normed real
algebra, with its exponential charts) and a left Haar measure `μ` on `G`:

* `IsExpLieAlgebra.exists_eq_sum_convolutionIntegral`: every smooth compactly supported `f : G → ℂ`
  is a finite sum `f = ∑ᵢ φᵢ ⋆ ψᵢ` of convolutions of smooth functions, with `φᵢ` compactly supported
  in a prescribed neighbourhood of `1` and `ψᵢ` supported in the support of `f`;
* `IsExpLieAlgebra.exists_eq_sum_integral_revProdExp`: the explicit form behind it,
  `f x = ∑ᵢ ∫ Kᵢ(t) Fᵢ(exp (t_{d-1} X_{d-1}) ⋯ exp (t₀ X₀) · x) dt` for any `X : Fin d → 𝔤`, with smooth
  kernels `Kᵢ` supported in a prescribed ball and smooth `Fᵢ` supported in the support of `f`.

The proof follows Dixmier and Malliavin: the one-variable lemma
(`Langlands.Analysis.DixmierMalliavin.exists_dirac_eq_tsum_iteratedDeriv_add`) applied to
`t ↦ f (exp (t X) x)` decomposes `f` in the direction `X`
(`IsExpLieAlgebra.exists_eq_integral_add_integral_direction`); iterating over a basis of `𝔤` gives
the explicit form; and the Haar density in coordinates of the second kind (`HaarDensity`) turns each
average into a convolution.
-/

namespace Langlands.LinearLieGroup

open Langlands.Analysis.DixmierMalliavin
open scoped Manifold ContDiff Topology
open NormedSpace Set MeasureTheory Metric

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)

namespace IsExpLieAlgebra

/-- **The decomposition in one direction.** For smooth compactly supported `f`, `X ∈ 𝔤` and `ε > 0`
there are a smooth `f₁` supported in the support of `f` and smooth `g`, `k` on `ℝ` supported in
`[0, ε]` with `f x = ∫ g(t) f₁(exp (t X) x) dt + ∫ k(t) f(exp (t X) x) dt` for all `x`. Here
`f₁ = ∑ c_p dirDeriv X p f` for the coefficients of the one-variable lemma applied with the bounds
`M` of `exists_bound_dirDeriv`. -/
theorem exists_eq_integral_add_integral_direction {f : G → ℂ}
    (hf : letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ f)
    (hfc : HasCompactSupport f) (X : 𝔤) {ε : ℝ} (hε : 0 < ε) :
    ∃ f₁ : G → ℂ, (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ f₁) ∧
      tsupport f₁ ⊆ tsupport f ∧
      ∃ g k : ℝ → ℂ, ContDiff ℝ ∞ g ∧ ContDiff ℝ ∞ k ∧ tsupport g ⊆ Icc 0 ε ∧
        tsupport k ⊆ Icc 0 ε ∧
        ∀ x, f x = (∫ t, g t * f₁ (h.expG (t • X) * x)) + ∫ t, k t * f (h.expG (t • X) * x) := by
  obtain ⟨M, hM, hser⟩ := h.exists_bound_dirDeriv hf hfc X
  obtain ⟨c, g, k, hg, hk, hgs, hks, hc, hid⟩ := exists_dirac_eq_tsum_iteratedDeriv_add M hε
  obtain ⟨hf₁, -⟩ := hser c hc
  refine ⟨_, hf₁, closure_minimal (fun x hx => by_contra fun hx' => hx (by
    simp [h.dirDeriv_eq_zero_of_notMem X _ hx'])) (isClosed_tsupport f), g, k, hg, hk, hgs, hks, fun x => ?_⟩
  set F : ℝ → ℂ := fun t => f (h.expG (t • X) * x) with hFdef
  have hF : ContDiff ℝ ∞ F := h.contDiff_comp_expG_smul_mul hf X x
  have hD : ∀ p t, iteratedDeriv p F t = h.dirDeriv X p f (h.expG (t • X) * x) :=
    fun p t => h.iteratedDeriv_comp_expG_mul X p f x t
  have key := hid F hF (fun p t _ => by rw [hD]; exact hM p _)
  have hF0 : F 0 = f x := by
    simp only [hFdef, zero_smul]; rw [h.expG_zero, one_mul]
  rw [hF0] at key
  rw [key]
  congr 1
  · have hgc : HasCompactSupport g := isCompact_Icc.of_isClosed_subset (isClosed_tsupport g) hgs
    have hcont : ∀ p, Continuous (fun t => iteratedDeriv p F t) := fun p =>
      hF.continuous_iteratedDeriv p (by exact_mod_cast le_top)
    let T : ℕ → ℝ → ℂ := fun p t => (c p : ℂ) * (iteratedDeriv p F t * g t)
    have hTi : ∀ p, Integrable (T p) := fun p =>
      (((hcont p).mul hg.continuous).integrable_of_hasCompactSupport hgc.mul_left).const_mul _
    have hTb : ∀ p t, ‖T p t‖ ≤ |c p| * M p * ‖g t‖ := by
      intro p t
      simp only [T, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      rw [mul_assoc (|c p|)]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg (c p))
      have : ‖iteratedDeriv p F t‖ ≤ M p := by rw [hD]; exact hM p _
      exact mul_le_mul_of_nonneg_right this (norm_nonneg _)
    have hgi : Integrable (fun t => ‖g t‖) :=
      (hg.continuous.integrable_of_hasCompactSupport hgc).norm
    have hsum : Summable fun p => ∫ t, ‖T p t‖ := by
      refine Summable.of_nonneg_of_le (fun p => integral_nonneg fun t => norm_nonneg _)
        (fun p => ?_) (hc.mul_right (∫ t, ‖g t‖))
      rw [← integral_const_mul]
      exact integral_mono (hTi p).norm (hgi.const_mul _) (fun t => hTb p t)
    have e1 : ∀ p, (c p : ℂ) * ∫ t, iteratedDeriv p F t * g t = ∫ t, T p t := fun p =>
      (integral_const_mul _ _).symm
    simp_rw [e1]
    rw [integral_tsum_of_summable_integral_norm hTi hsum]
    congr 1
    funext t
    simp only [T, hD]
    rw [← tsum_mul_left]
    congr 1
    funext p
    ring
  · congr 1; funext t; rw [mul_comm]

/-- **The explicit form.** For smooth compactly supported `f`, `ε > 0` and `X : Fin d → 𝔤`, `f` is a
finite sum `f x = ∑ᵢ ∫ Kᵢ(t) Fᵢ(revProdExp X t · x) dt` of averages of left translates of smooth
functions `Fᵢ` supported in the support of `f`, against smooth kernels `Kᵢ` on `ℝ^d` supported in the
closed `ε`-ball. Induction on `d`, with `exists_eq_integral_add_integral_direction` in the direction
`X₀` applied to `f` and its expansion over the remaining directions applied to both `f₁` and `f`. -/
theorem exists_eq_sum_integral_revProdExp {ε : ℝ} (hε : 0 < ε) : ∀ {d : ℕ} (X : Fin d → 𝔤)
    (f : G → ℂ),
    (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ f) → HasCompactSupport f →
    ∃ (m : ℕ) (F : Fin m → G → ℂ) (K : Fin m → (Fin d → ℝ) → ℂ),
      (∀ i, (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ (F i)) ∧
        tsupport (F i) ⊆ tsupport f) ∧
      (∀ i, ContDiff ℝ ∞ (K i) ∧ tsupport (K i) ⊆ Metric.closedBall 0 ε) ∧
      ∀ x, f x = ∑ i, ∫ t, K i t * F i (h.revProdExp X t * x)
  | 0, X, f, hf, hfc => by
    refine ⟨1, fun _ => f, fun _ _ => 1, fun _ => ⟨hf, subset_rfl⟩, fun _ => ⟨contDiff_const, ?_⟩,
      fun x => ?_⟩
    · intro t _
      rw [Subsingleton.elim t 0]; exact Metric.mem_closedBall_self hε.le
    · have hv : (volume : Measure (Fin 0 → ℝ)).real univ = 1 := by
        simp [Measure.real, MeasureTheory.volume_pi]
      simp [h.revProdExp_zero, hv]
  | d + 1, X, f, hf, hfc => by
    let := h.chartedSpace
    obtain ⟨f₁, hf₁, hf₁c, g, k, hg, hk, hgs, hks, hdec⟩ :=
      exists_eq_integral_add_integral_direction h hf hfc (X 0) hε
    replace hgs : tsupport g ⊆ Icc (-ε) ε := hgs.trans (Icc_subset_Icc (by linarith) le_rfl)
    replace hks : tsupport k ⊆ Icc (-ε) ε := hks.trans (Icc_subset_Icc (by linarith) le_rfl)
    obtain ⟨m₁, F₁, K₁, hF₁, hK₁, hd₁⟩ :=
        exists_eq_sum_integral_revProdExp hε (Fin.tail X) f₁ hf₁
            (hfc.of_isClosed_subset (isClosed_tsupport _) hf₁c)
    obtain ⟨m₂, F₂, K₂, hF₂, hK₂, hd₂⟩ := exists_eq_sum_integral_revProdExp hε (Fin.tail X) f hf hfc
    refine ⟨m₁ + m₂, Fin.append F₁ F₂,
      Fin.append (fun i t => g (t 0) * K₁ i (Fin.tail t)) (fun i t => k (t 0) * K₂ i (Fin.tail t)),
      ?_, ?_, ?_⟩
    · intro i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simpa only [Fin.append_left] using And.intro (hF₁ i).1 ((hF₁ i).2.trans hf₁c)
      · simpa only [Fin.append_right] using hF₂ i
    · intro i
      refine Fin.addCases (fun i => ?_) (fun i => ?_) i
      · simp only [Fin.append_left]
        exact ⟨contDiff_cons_kernel hg (hK₁ i).1, tsupport_cons_kernel hε.le hgs (hK₁ i).2⟩
      · simp only [Fin.append_right]
        exact ⟨contDiff_cons_kernel hk (hK₂ i).1, tsupport_cons_kernel hε.le hks (hK₂ i).2⟩
    · intro x
      rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
      rw [hdec x]
      congr 1
      · exact (h.sum_integral_cons_kernel X hε.le hg.continuous hgs (fun i => (hK₁ i).1.continuous)
          (fun i => (hK₁ i).2) (fun i => (hF₁ i).1.continuous) hd₁ x).symm
      · exact (h.sum_integral_cons_kernel X hε.le hk.continuous hks (fun i => (hK₂ i).1.continuous)
          (fun i => (hK₂ i).2) (fun i => (hF₂ i).1.continuous) hd₂ x).symm
include h in
/-- **Dixmier–Malliavin on a linear Lie group.** For a left Haar measure `μ` on `G`, a neighbourhood `U`
of `1` and a smooth compactly supported `f`, there are smooth `φᵢ`, `ψᵢ` (`i < n`), the `φᵢ` compactly
supported in `U` and the `ψᵢ` supported in the support of `f`, with
`f = ∑ᵢ φᵢ ⋆ ψᵢ` (`Langlands.Hecke.convolutionIntegral μ`). Take the explicit form for a basis of `𝔤`
and `ε` small; each average `x ↦ ∫ Kᵢ(t) Fᵢ(revProdExp t · x) dt` is `κᵢ ⋆ Fᵢ` for the function `κᵢ` on
`G` whose pull-back to `ℝ^d` by the coordinates of the second kind is `t ↦ Kᵢ(-t)`
(`exists_smooth_density_prodExp`), using `(revProdExp t)⁻¹ = prodExp (-t)`. -/
theorem exists_eq_sum_convolutionIntegral [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] {U : Set G} (hU : U ∈ 𝓝 1) (f : G → ℂ)
    (hf : letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ f) (hfc : HasCompactSupport f) :
    ∃ (n : ℕ) (φ ψ : Fin n → G → ℂ),
      (∀ i, (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ (φ i)) ∧
        HasCompactSupport (φ i) ∧ tsupport (φ i) ⊆ U ∧
        (letI := h.chartedSpace; ContMDiff 𝓘(ℝ, 𝔤) 𝓘(ℝ, ℂ) ∞ (ψ i)) ∧
        tsupport (ψ i) ⊆ tsupport f) ∧
      f = ∑ i, Langlands.Hecke.convolutionIntegral μ (φ i) (ψ i) := by
  let := h.chartedSpace
  let b := Module.finBasis ℝ 𝔤
  obtain ⟨ε₀, hε₀, hdens⟩ := exists_smooth_density_prodExp h μ b
  have hP0 : h.prodExp (⇑b) 0 = 1 :=
      Subtype.ext (Units.ext (by rw [h.val_prodExp, prodExpVal_zero]; rfl))
  obtain ⟨ε₁, hε₁, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.1
    ((h.continuous_prodExp (⇑b)).continuousAt.preimage_mem_nhds (t := U) (x := 0) (by rwa [hP0]))
  obtain ⟨ε, hε, he₀, he₁⟩ : ∃ ε : ℝ, 0 < ε ∧ ε ≤ ε₀ ∧ ε ≤ ε₁ :=
      ⟨min ε₀ ε₁, lt_min hε₀ hε₁, min_le_left _ _, min_le_right _ _⟩
  obtain ⟨m, F, K, hF, hK, hd⟩ := exists_eq_sum_integral_revProdExp h hε (⇑b) f hf hfc
  have hK' : ∀ i, ContDiff ℝ ∞ (fun t => K i (-t)) ∧
      tsupport (fun t => K i (-t)) ⊆ Metric.closedBall 0 ε := by
    intro i
    refine ⟨(hK i).1.comp contDiff_neg, ?_⟩
    intro t ht
    have : -t ∈ tsupport (K i) := by
      have := tsupport_comp_subset_preimage (K i) (f := fun t : Fin _ → ℝ => -t) continuous_neg ht
      simpa using this
    have := (hK i).2 this
    simpa [mem_closedBall_zero_iff, norm_neg] using this
  choose κ hκs hκc hκV hκ using fun i => hdens ε he₀ (fun t => K i (-t)) (hK' i).1 (hK' i).2
  refine ⟨m, κ, F, fun i => ⟨hκs i, hκc i,
    (hκV i).trans (image_subset_iff.2 ((Metric.closedBall_subset_closedBall he₁).trans hball)),
    (hF i).1, (hF i).2⟩, ?_⟩
  funext x
  rw [hd x, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Langlands.Hecke.convolutionIntegral, hκ i (fun y => F i (y⁻¹ * x))
    ((hF i).1.continuous.comp (continuous_inv.mul continuous_const))]
  have e : ∀ t : Fin (Module.finrank ℝ 𝔤) → ℝ, K i (-t) * F i ((h.prodExp (⇑b) t)⁻¹ * x) =
      (fun s => K i s * F i (h.revProdExp (⇑b) s * x)) (-t) := by
    intro t
    have := h.revProdExp_inv (⇑b) (-t)
    rw [neg_neg] at this
    simp only [← this, inv_inv]
  simp_rw [e]
  exact (integral_neg_eq_self (fun s => K i s * F i (h.revProdExp (⇑b) s * x)) volume).symm

end IsExpLieAlgebra

end Langlands.LinearLieGroup
