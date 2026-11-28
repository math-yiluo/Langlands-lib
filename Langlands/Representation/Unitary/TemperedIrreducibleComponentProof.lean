import Langlands.Representation.Unitary.TemperedComponentFibre
import Langlands.Representation.Unitary.TemperedComponentIntertwiner
import Langlands.Representation.Unitary.TemperedIrreducibleComponentStatement
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Proof of the irreducible tempered component theorem

This module proves `Langlands.Analysis.TemperedIrreducibleComponentStatement`. The test functions
`ψ_k` are an approximate identity `χ_n` together with the given countable family `Φ`; the global
kernel of the projected adjoints `P₀ (j ∘ π(ψ_k))^*`, scaled to weighted trace one, is a nonzero
point of the compact convex set `coneSet`. A nonzero extreme point of that set gives the irreducible unitary
representation `σ` on the Hilbert space of its left-ideal kernel, the bounded maps `B_k`, and from
them the subspace `D` and the equivariant map `J`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped InnerProductSpace ComplexConjugate ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Langlands.Analysis.TemperedComponent

open Langlands.Archimedean Langlands.Analysis.KernelCone Langlands.Analysis.OperatorIdeals

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  {μ : Measure G} [μ.IsHaarMeasure]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W]

/-- A bounded operator vanishing on a Hilbert basis is zero. -/
theorem eq_zero_of_hilbertBasis {β E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (e : HilbertBasis β ℂ W) (A : W →L[ℂ] E) (h : ∀ b, A (e b) = 0) : A = 0 := by
  ext w
  have hs := A.hasSum (e.hasSum_repr w)
  simp only [map_smul, h, smul_zero] at hs
  rw [hs.unique hasSum_zero, zero_apply]

/-- The closure of `j(H₀)` is invariant. -/
theorem wSub_invariant {π : G →* (H →L[ℂ] H)} {πW : G →* (W →L[ℂ] W)} (j : H →L[ℂ] W)
    (hj : ∀ g x, j (π g x) = πW g (j x)) (H₀ : Submodule ℂ H) (hH₀ : ∀ g, ∀ x ∈ H₀, π g x ∈ H₀)
    (g : G) : ∀ w ∈ wSub j H₀, πW g w ∈ wSub j H₀ := by
  have hle : H₀.map (j : H →ₗ[ℂ] W) ≤ (wSub j H₀).comap (πW g : W →ₗ[ℂ] W) := by
    rintro _ ⟨x, hx, rfl⟩
    change πW g (j x) ∈ wSub j H₀
    rw [← hj]
    exact Submodule.le_topologicalClosure _ (Submodule.mem_map_of_mem (hH₀ g x hx))
  have hcl : IsClosed (((wSub j H₀).comap (πW g : W →ₗ[ℂ] W) : Submodule ℂ W) : Set W) :=
    (Submodule.isClosed_topologicalClosure _).preimage (πW g).continuous
  exact fun w hw => Submodule.topologicalClosure_minimal _ hle hcl hw

end Langlands.Analysis.TemperedComponent

namespace Langlands.Analysis

open Langlands.Archimedean Langlands.Analysis.KernelCone Langlands.Analysis.OperatorIdeals
open Langlands.Analysis.TemperedComponent

/-- **Irreducible tempered components** (Bernstein 1988, §§1.2–1.5, single-fibre form). -/
theorem temperedIrreducibleComponent : TemperedIrreducibleComponentStatement := by
  intro G _ _ _ _ _ _ _ _ μ _ H _ _ _ π hπu hπ H₀ hH₀c hH₀ hH₀ne W _ _ _ πW hπW j hjinj hj
    hHS Φ hΦc hΦ
  have : CompleteSpace H₀ := hH₀c.completeSpace_coe
  -- test functions: an approximate identity and the family `Φ`
  obtain ⟨χ, hχ⟩ := exists_approxIdentity μ
  let κ : Type := ℕ ⊕ Φ
  let ψ : κ → G → ℂ := Sum.elim χ fun φ => (φ : G → ℂ)
  have hψ : ∀ k, IsTestFunction (ψ k) := by
    rintro (n | ⟨φ, hφ⟩)
    · exact hχ.test n
    · exact hΦ φ hφ
  let nIdx : ℕ → κ := Sum.inl
  have hχ' : IsApproxIdentity μ fun n => ψ (nIdx n) := hχ
  -- a Hilbert basis of `W` and the Hilbert–Schmidt sums
  obtain ⟨s, e, -⟩ := exists_hilbertBasis ℂ W
  have hHSk : ∀ k, Summable fun b => ‖ContinuousLinearMap.adjoint (opT μ π hπ j ψ hψ k) (e b)‖ ^ 2 := by
    intro k
    obtain ⟨T, hT, hTHS⟩ := hHS (ψ k) (hψ k).1 (hψ k).2.1 (hψ k).2.2
    have hTeq : T = opT μ π hπ j ψ hψ k := by
      ext x; rw [hT]; rfl
    obtain ⟨t, d, hd⟩ := isHilbertSchmidt_adjoint T hTHS
    rw [← hTeq]
    exact (hilbertSchmidtBasisIndependence W H t s (ContinuousLinearMap.adjoint T) d e).1.mp hd
  have hSk : ∀ k, Summable fun b => ‖opA μ π hπ j H₀ ψ hψ k (e b)‖ ^ 2 := fun k =>
    (hHSk k).of_nonneg_of_le (fun _ => sq_nonneg _) fun b =>
      pow_le_pow_left₀ (norm_nonneg _) (H₀.norm_starProjection_apply_le _) 2
  -- weights
  let S : κ → ℝ := fun k => ∑' b, ‖opA μ π hπ j H₀ ψ hψ k (e b)‖ ^ 2
  have hS0 : ∀ k, 0 ≤ S k := fun k => tsum_nonneg fun _ => sq_nonneg _
  have : Countable κ := by
    have := hΦc.to_subtype
    infer_instance
  obtain ⟨enc, henc⟩ := Countable.exists_injective_nat κ
  let c : κ → ℝ := fun k => (1 / 2 : ℝ) ^ enc k / (1 + S k)
  have hc : ∀ k, 0 < c k := fun k => div_pos (pow_pos (by norm_num) _) (by linarith [hS0 k])
  have hcS : ∀ k, c k * S k ≤ (1 / 2 : ℝ) ^ enc k := fun k => by
    have h1 : S k / (1 + S k) ≤ 1 := (div_le_one (by linarith [hS0 k])).mpr (by linarith)
    calc c k * S k = (1 / 2 : ℝ) ^ enc k * (S k / (1 + S k)) := by
          simp only [c]; ring
      _ ≤ (1 / 2 : ℝ) ^ enc k * 1 :=
          mul_le_mul_of_nonneg_left h1 (pow_nonneg (by norm_num) _)
      _ = _ := mul_one _
  -- the global kernel
  let F₀ := globalKernel μ π hπ j H₀ ψ hψ
  have hC₀ : IsConeElement (globalRel μ π hπ πW hπW j H₀ ψ hψ hπu nIdx) F₀ :=
    isConeElement_globalKernel (hj := hj) (hπu := hπu) (hH₀c := hH₀c) (hH₀ := hH₀) μ π hπ πW hπW
      j H₀ ψ hψ nIdx
  have hB₀ : IsBoundedForm F₀ :=
    isBoundedForm_globalKernel (hπu := hπu) (hH₀c := hH₀c) μ π hπ j H₀ ψ hψ
  have htrace : traceW c e F₀ =
      ∑' k, ENNReal.ofReal (c k * S k) := by
    rw [traceW, ENNReal.tsum_prod']
    refine tsum_congr fun k => ?_
    simp only [F₀, re_globalKernel_diag]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun b => mul_nonneg (hc k).le (sq_nonneg _))
      ((hSk k).mul_left (c k)), tsum_mul_left]
  have htop : traceW c e F₀ ≠ ⊤ := by
    rw [htrace]
    refine ne_top_of_le_ne_top (b := ∑' n : ℕ, (2⁻¹ : ℝ≥0∞) ^ n) ?_ ?_
    · rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
      exact ENNReal.ofNat_ne_top
    · calc ∑' k, ENNReal.ofReal (c k * S k) ≤ ∑' k, (2⁻¹ : ℝ≥0∞) ^ enc k := by
            refine ENNReal.tsum_le_tsum fun k => ?_
            calc ENNReal.ofReal (c k * S k) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ enc k) :=
                  ENNReal.ofReal_le_ofReal (hcS k)
              _ = (2⁻¹ : ℝ≥0∞) ^ enc k := by
                  rw [ENNReal.ofReal_pow (by norm_num), one_div, ENNReal.ofReal_inv_of_pos
                    (by norm_num), ENNReal.ofReal_ofNat]
        _ ≤ ∑' n : ℕ, (2⁻¹ : ℝ≥0∞) ^ n :=
            ENNReal.tsum_comp_le_tsum_of_injective henc fun n => (2⁻¹ : ℝ≥0∞) ^ n
  -- the global kernel is nonzero
  have hA : ∃ k b, opA μ π hπ j H₀ ψ hψ k (e b) ≠ 0 := by
    obtain ⟨h₀, hh₀, hh₀ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hH₀ne
    have hjh : j h₀ ≠ 0 := fun h => hh₀ne (hjinj (h.trans (map_zero j).symm))
    have hlim : Tendsto (fun n => j (testOp μ π hπ (χ n) (hχ.test n) h₀)) atTop (𝓝 (j h₀)) :=
      (j.continuous.tendsto _).comp (hχ.tendsto π hπ h₀)
    obtain ⟨n, hn⟩ := (hlim.eventually_ne hjh).exists
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    have hzero : opA μ π hπ j H₀ ψ hψ (nIdx n) = 0 :=
      eq_zero_of_hilbertBasis e _ (hcon (nIdx n))
    have hadj := congrArg (fun A => ContinuousLinearMap.adjoint A h₀) hzero
    simp only [map_zero, zero_apply] at hadj
    rw [adjoint_opA, ContinuousLinearMap.comp_apply,
      (Submodule.starProjection_eq_self_iff (K := H₀)).mpr hh₀] at hadj
    exact hn hadj
  have h0 : traceW c e F₀ ≠ 0 := by
    obtain ⟨k, b, hkb⟩ := hA
    intro hz
    rw [traceW, ENNReal.tsum_eq_zero] at hz
    have := hz (k, b)
    simp only [F₀, re_globalKernel_diag, ENNReal.ofReal_eq_zero] at this
    have hpos : 0 < c k * ‖opA μ π hπ j H₀ ψ hψ k (e b)‖ ^ 2 :=
      mul_pos (hc k) (pow_pos (norm_pos_iff.mpr hkb) 2)
    linarith
  have hF₀mem := smul_inv_mem_coneSet hc hC₀ hB₀ h0 htop
  have hF₀ne : ((traceW c e F₀).toReal)⁻¹ • F₀ ≠ 0 := by
    intro hz
    have h1 := traceW_smul (c := c) (e := e) (F := F₀)
      (inv_nonneg.mpr (ENNReal.toReal_nonneg (a := traceW c e F₀)))
    rw [hz] at h1
    have h2 : traceW c e (0 : Coord (algebra μ π hπ) κ W → ℂ) = 0 := by simp [traceW]
    rw [h2] at h1
    have hpos : 0 < (traceW c e F₀).toReal := ENNReal.toReal_pos h0 htop
    rcases mul_eq_zero.mp h1.symm with h | h
    · rw [ENNReal.ofReal_eq_zero] at h
      linarith [inv_pos.mpr hpos]
    · exact h0 h
  -- a nonzero extreme point
  obtain ⟨F, hFext, hFne⟩ := exists_extremePoint_ne_zero c e hF₀mem hF₀ne
  have hC : IsConeElement (globalRel μ π hπ πW hπW j H₀ ψ hψ hπu nIdx) F := hFext.1.1.1
  have hB : IsBoundedForm F := isBoundedForm_of_mem hFext.1
  -- the representation and the maps `B_k`
  obtain ⟨k₀, v₀, hkv⟩ := exists_opB_ne_zero hC hB hχ' hFne
  have hV : Nontrivial (VL hC) := by
    refine ⟨⟨v₀, 0, fun h => hkv ?_⟩⟩
    rw [h, map_zero]
  have hσ := isContinuousRepresentation_sigma hC hπu
  have hirr := isTopologicallyIrreducible_sigma hC hπu hc hFext hFne hV
  obtain ⟨D, J, hJg, hJφ, hJne, hJW⟩ := exists_intertwiner (sigma hC hπu) hσ πW hπW ψ hψ nIdx hχ'
    (opB hC hB) (wSub j H₀) (Submodule.isClosed_topologicalClosure _)
    (wSub_invariant j hj H₀ hH₀) (opB_mem_wSub hC hB) (opB_relation hC hB) ⟨k₀, v₀, hkv⟩
  refine ⟨VL hC, inferInstance, inferInstance, inferInstance, sigma hC hπu, D, J,
    sigma_mem_unitary hC hπu, hσ, hirr, hJg, fun φ hm hb hcs => ?_, hJne, fun d hd => ?_⟩
  · obtain ⟨h1, h2⟩ := hJφ φ ⟨hm, hb, hcs⟩
    refine ⟨h1, fun ψ' hψ' => ?_⟩
    exact h2 (Sum.inr ⟨ψ', hψ'⟩)
  · have := hJW d hd
    rwa [← SetLike.mem_coe, coe_wSub] at this

end Langlands.Analysis
