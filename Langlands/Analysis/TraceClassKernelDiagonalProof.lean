import Langlands.Analysis.TraceClassKernelDiagonalStatement
import Langlands.Analysis.TraceClassKernelDiagonalCore
import Langlands.Analysis.TraceClassFactorizationProof
import Langlands.Analysis.HilbertSchmidtBasisProof
import Langlands.Analysis.HilbertSchmidtIdealProof
import Langlands.Analysis.HilbertSchmidtProductTraceProof
import Langlands.Analysis.OperatorTraceProof
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Trace of a trace-class integral operator as a diagonal integral

Brislawn, *Traceable integral kernels on countably generated measure spaces*,
Corollary 3.2. The proof tests the operator on indicators, then uses square-cell
averages to identify the diagonal a.e.
-/

noncomputable section

open MeasureTheory Filter
open scoped ComplexConjugate

namespace Langlands.Analysis.OperatorIdeals

open KernelDiagonal

universe u

private theorem exists_traceClass_expansion (E : Type u) [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] (T : E →L[ℂ] E) (hT : IsTraceClass T) :
    ∃ ι : Type u, Countable ι ∧ ∃ a b : ι → E,
      (Summable fun i => ‖a i‖ ^ 2) ∧ (Summable fun i => ‖b i‖ ^ 2) ∧
      (∀ z : E, HasSum (fun i => inner ℂ (b i) z • a i) (T z)) ∧
      HasSum (fun i => inner ℂ (b i) (a i)) (operatorTrace T) := by
  obtain ⟨B, C, hB, hC, rfl⟩ := traceClassFactorization E T hT
  obtain ⟨w, d, _⟩ := exists_hilbertBasis ℂ E
  have hs (A : E →L[ℂ] E) (hA : IsHilbertSchmidt A) : Summable (fun i => ‖A (d i)‖ ^ 2) := by
    obtain ⟨w', d', h'⟩ := hA
    exact (hilbertSchmidtBasisIndependence E E w' w A d' d).1.mp h'
  have hsB := hs B hB
  have hsC := hs C.adjoint (isHilbertSchmidt_adjoint C hC)
  let s := Function.support (fun i : w => ‖B (d i)‖ ^ 2)
  have h₀ (i : w) (hi : i ∉ s) : B (d i) = 0 := by
    simpa [s, Function.mem_support] using hi
  refine ⟨s, hsB.countable_support, (fun i => B (d i)), (fun i => C.adjoint (d i)),
    hsB.subtype s, hsC.subtype s, ?_, ?_⟩
  · intro z
    have hAll : HasSum (fun i : w => inner ℂ (C.adjoint (d i)) z • B (d i)) ((B.comp C) z) := by
      simpa only [map_smul, d.repr_apply_apply, C.adjoint_inner_left, ContinuousLinearMap.comp_apply]
        using B.hasSum (d.hasSum_repr (C z))
    refine (hasSum_subtype_iff_of_support_subset ?_).2 hAll
    intro i hi
    by_contra h
    exact hi (by simp [h₀ i h])
  · have hprod := hilbertSchmidtProductTrace E E w w B C d d hB hC
    have hEq : traceIn d (C.comp B) = operatorTrace (B.comp C) :=
      hprod.2.2.trans (operatorTraceBasis E (B.comp C) w d hT).2.symm
    have hAll : HasSum (fun i : w => inner ℂ (C.adjoint (d i)) (B (d i)))
        (operatorTrace (B.comp C)) := by
      rw [← hEq]
      simpa only [C.adjoint_inner_left, ContinuousLinearMap.comp_apply, traceIn] using
        hprod.1.of_norm.hasSum
    refine (hasSum_subtype_iff_of_support_subset ?_).2 hAll
    intro i hi
    by_contra h
    exact hi (by simp [h₀ i h])

section Integral

variable {X ι : Type*} [MeasurableSpace X] {μ : Measure X}

private lemma integral_sq_norm_L2 (f : Lp ℂ 2 μ) : (∫ x, ‖f x‖ ^ 2 ∂μ) = ‖f‖ ^ 2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def, ← integral_re (L2.integrable_inner f f)]
  simp only [← norm_sq_eq_re_inner (𝕜 := ℂ)]

private lemma integral_square_eq_tsum [SigmaFinite μ] {T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ}
    {K : X → X → ℂ} {a b : ι → Lp ℂ 2 μ}
    (hK : MemLp (Function.uncurry K) 2 (μ.prod μ))
    (hTK : ∀ φ : Lp ℂ 2 μ, (T φ : X → ℂ) =ᵐ[μ] fun x => ∫ y, K x y * φ y ∂μ)
    (hT : ∀ φ : Lp ℂ 2 μ, HasSum (fun i => inner ℂ (b i) φ • a i) (T φ))
    {A : Set X} (hA : MeasurableSet A) (hμA : μ A ≠ ⊤) :
    ∫ p in A ×ˢ A, Function.uncurry K p ∂(μ.prod μ) =
      ∑' i, (∫ y in A, a i y ∂μ) * conj (∫ y in A, b i y ∂μ) := by
  let φ := indicatorConstLp 2 hA hμA (1 : ℂ)
  have hφ : (φ : X → ℂ) =ᵐ[μ] A.indicator (fun _ => 1) := indicatorConstLp_coeFn
  have hpair (f : Lp ℂ 2 μ) : inner ℂ φ f = ∫ x in A, f x ∂μ :=
    L2.inner_indicatorConstLp_one hA hμA f
  let _ : IsFiniteMeasure (μ.restrict A) := isFiniteMeasure_restrict.2 hμA
  have hIK : IntegrableOn (Function.uncurry K) (A ×ˢ A) (μ.prod μ) := by
    rw [IntegrableOn, ← Measure.prod_restrict]
    exact (hK.mono_measure (Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self)).integrable
      (by norm_num)
  calc
    _ = ∫ x in A, ∫ y in A, K x y ∂μ ∂μ := setIntegral_prod _ hIK
    _ = inner ℂ φ (T φ) := by
      rw [hpair]
      symm
      apply integral_congr_ae
      refine ae_restrict_of_ae ?_
      filter_upwards [hTK φ] with x hx
      rw [hx, ← integral_indicator hA]
      apply integral_congr_ae
      filter_upwards [hφ] with y hy
      by_cases h : y ∈ A <;> simp [hy, h]
    _ = _ := by
      have hv := (innerSL ℂ φ).hasSum (hT φ)
      change innerSL ℂ φ (T φ) = _
      rw [← hv.tsum_eq]
      apply tsum_congr
      intro i
      rw [innerSL_apply_apply, inner_smul_right, hpair, ← inner_conj_symm (𝕜 := ℂ) (b i) φ,
        hpair, mul_comm]

end Integral

/-- The diagonal of the supplied kernel is integrable, and its integral is the operator trace. -/
theorem traceClassContinuousKernelDiagonal : TraceClassContinuousKernelDiagonalStatement.{u} := by
  intro X _ _ _ _ μ _ T K hT hK hTK hc
  obtain ⟨ι, hι, a, b, ha, hb, happly, htrace⟩ := exists_traceClass_expansion (Lp ℂ 2 μ) T hT
  let _ : Countable ι := hι
  let w (i : ι) (x : X) := energy (a i x) (b i x)
  have ha₂ (i : ι) := (memLp_two_iff_integrable_sq_norm (Lp.memLp (a i)).aestronglyMeasurable).1
    (Lp.memLp (a i))
  have hb₂ (i : ι) := (memLp_two_iff_integrable_sq_norm (Lp.memLp (b i)).aestronglyMeasurable).1
    (Lp.memLp (b i))
  have hw (i : ι) : Integrable (w i) μ := ((ha₂ i).add (hb₂ i)).div_const 2
  have hws : Summable (fun i => ∫ x, ‖w i x‖ ∂μ) := by
    have hEq (i : ι) : (∫ x, ‖w i x‖ ∂μ) = (‖a i‖ ^ 2 + ‖b i‖ ^ 2) / 2 := by
      have hn (x : X) : ‖w i x‖ = w i x := Real.norm_of_nonneg (energy_nonneg _ _)
      simp only [hn]
      simp only [w, energy, integral_div, integral_add (ha₂ i) (hb₂ i), integral_sq_norm_L2]
    simpa only [hEq] using (ha.add hb).div_const 2
  let g (i : ι) (x : X) := a i x * conj (b i x)
  have hg (i : ι) : Integrable (g i) μ := by
    change Integrable (fun x => inner ℂ (b i x) (a i x)) μ
    exact L2.integrable_inner (b i) (a i)
  have hgs : Summable (fun i => ∫ x, ‖g i x‖ ∂μ) := hws.of_nonneg_of_le
    (fun _ => integral_nonneg fun _ => norm_nonneg _)
    (fun i => integral_mono (hg i).norm (hw i).norm fun _ =>
      (norm_mul_conj_le_energy _ _).trans (Real.le_norm_self _))
  have hd : Integrable (fun x => ∑' i, g i x) μ := integrable_tsum_of_summable_integral_norm hg hgs
  have hAe : (fun x => K x x) =ᵐ[μ] (fun x => ∑' i, g i x) := by
    change ∀ᵐ x ∂μ, K x x = ∑' i, g i x
    rw [← Measure.restrict_univ (μ := μ), ← iUnion_spanningSets μ, ae_restrict_iUnion_iff]
    intro j
    let S := spanningSets μ j
    let ν := μ.restrict S
    have hS := measurableSet_spanningSets μ j
    have hμS := (measure_spanningSets_lt_top μ j).ne
    let _ : IsFiniteMeasure ν := isFiniteMeasure_restrict.2 hμS
    have hν : ν ≤ μ := Measure.restrict_le_self
    refine ae_eq_diagonal_tsum (ν := ν) (a := fun i x => a i x) (b := fun i x => b i x)
      (fun i => (Lp.memLp (a i)).mono_measure hν) (fun i => (Lp.memLp (b i)).mono_measure hν)
      (summable_integral_norm_mono_measure hν hw hws)
      ((hK.mono_measure (Measure.prod_mono hν hν)).integrable (by norm_num)) ?_
      (ae_restrict_of_ae hc)
    intro A hA
    have hμAS : μ (A ∩ S) ≠ ⊤ := ((measure_mono Set.inter_subset_right).trans_lt hμS.lt_top).ne
    simpa only [ν, Measure.prod_restrict, Measure.restrict_restrict (hA.prod hA),
      Measure.restrict_restrict hA, Set.prod_inter_prod] using
      integral_square_eq_tsum hK hTK happly (hA.inter hS) hμAS
  refine ⟨hd.congr hAe.symm, ?_⟩
  calc
    operatorTrace T = ∑' i, inner ℂ (b i) (a i) := htrace.tsum_eq.symm
    _ = ∫ x, ∑' i, g i x ∂μ := by
      simpa only [L2.inner_def, RCLike.inner_apply, g] using
        integral_tsum_of_summable_integral_norm hg hgs
    _ = ∫ x, K x x ∂μ := integral_congr_ae hAe.symm

end Langlands.Analysis.OperatorIdeals
