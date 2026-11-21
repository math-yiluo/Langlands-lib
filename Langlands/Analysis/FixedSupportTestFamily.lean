import Mathlib.Analysis.Distribution.ContDiffMapSupportedIn
import Mathlib.Topology.ContinuousMap.Compact

/-! # Continuity of a jointly smooth family on a fixed compact support -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped ContDiff Distributions Topology

namespace Langlands.Analysis

universe uP uA

variable {P : Type uP} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {A : Type uA} [NormedAddCommGroup A] [NormedSpace ℝ A]

/-- A jointly smooth function has continuous derivatives in its second argument,
jointly in both the parameter and the argument. -/
theorem continuous_iteratedFDeriv_snd {H : P × A → ℂ} (hH : ContDiff ℝ ∞ H) (i : ℕ) :
    Continuous (fun p : P × A => iteratedFDeriv ℝ i (fun x => H (p.1, x)) p.2) := by
  let L : A →L[ℝ] P × A := ContinuousLinearMap.inr ℝ P A
  let C := ContinuousMultilinearMap.compContinuousLinearMapL (F := ℂ)
    (fun _ : Fin i => L)
  have he (p : P × A) :
      iteratedFDeriv ℝ i (fun x => H (p.1, x)) p.2 = C (iteratedFDeriv ℝ i H p) := by
    have hf : (fun x => H (p.1, x)) = (fun y : P × A => H ((p.1, 0) + y)) ∘ L := by
      funext x
      change H (p.1, x) = H (p.1 + 0, 0 + x)
      simp
    have hs : ContDiff ℝ ∞ (fun y : P × A => H ((p.1, 0) + y)) :=
      hH.comp (contDiff_const.add contDiff_id)
    rw [hf, L.iteratedFDeriv_comp_right hs _ (by simp), iteratedFDeriv_comp_add_left]
    change (iteratedFDeriv ℝ i H (p.1 + 0, 0 + p.2)).compContinuousLinearMap
      (fun _ => L) = _
    simp only [add_zero, zero_add]
    rfl
  simp_rw [he]
  exact C.continuous.comp (hH.continuous_iteratedFDeriv (by simp))

/-- Jointly smooth test functions with a common compact support
depend continuously on their parameter in the fixed-support test topology. -/
theorem continuousOn_fixedSupportTestFamily {H : P × A → ℂ} (hH : ContDiff ℝ ∞ H)
    {K : Compacts A} {s : Set P} (f : P → 𝓓_{K}(A, ℂ))
    (hf : ∀ p ∈ s, ∀ x : A, f p x = H (p, x)) :
    ContinuousOn f s := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp K.isCompact
  intro p hp
  apply (ContDiffMapSupportedIn.withSeminorms ℂ A ℂ ⊤ K).tendsto_nhds f (f p) |>.2
  intro i ε hε
  let M := ContinuousMultilinearMap ℝ (fun _ : Fin i => A) ℂ
  let D (q : P) : C(K, M) :=
    ⟨fun x => iteratedFDeriv ℝ i (fun y => H (q, y)) x.val,
      (continuous_iteratedFDeriv_snd hH i).comp (continuous_const.prodMk continuous_subtype_val)⟩
  have hD : Continuous D := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact (continuous_iteratedFDeriv_snd hH i).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hc : Continuous (fun q : P => D q - D p) :=
    hD.sub (continuous_const (y := D p))
  have hnorm : Continuous (fun z : C(K, M) => ‖z‖) :=
    @continuous_norm C(K, M) (inferInstance)
  have ho : IsOpen {q : P | ‖D q - D p‖ < ε} :=
    isOpen_lt (hnorm.comp hc) continuous_const
  have hmem : p ∈ {q : P | ‖D q - D p‖ < ε} := by
    change ‖D p - D p‖ < ε
    rw [sub_self, @norm_zero C(K, M) (inferInstance)]
    exact hε
  have hsmall : ∀ᶠ q in 𝓝[s] p, ‖D q - D p‖ < ε :=
    mem_nhdsWithin_of_mem_nhds (ho.mem_nhds hmem)
  filter_upwards [hsmall, self_mem_nhdsWithin] with q hq hqs
  have hdnonneg : 0 ≤ ‖D q - D p‖ := @norm_nonneg C(K, M) (inferInstance) (D q - D p)
  refine lt_of_le_of_lt ((ContDiffMapSupportedIn.seminorm_top_le_iff ℂ hdnonneg i _).2 ?_) hq
  intro x hx
  have hq' : (f q : A → ℂ) = fun y => H (q, y) := funext (hf q hqs)
  have hp' : (f p : A → ℂ) = fun y => H (p, y) := funext (hf p hp)
  change ‖iteratedFDeriv ℝ i ((f q : A → ℂ) - (f p : A → ℂ)) x‖ ≤ ‖D q - D p‖
  rw [iteratedFDeriv_sub_apply ((f q).contDiff.contDiffAt.of_le (by simp))
    ((f p).contDiff.contDiffAt.of_le (by simp)), hq', hp']
  exact (D q - D p).norm_coe_le_norm ⟨x, hx⟩

end Langlands.Analysis
