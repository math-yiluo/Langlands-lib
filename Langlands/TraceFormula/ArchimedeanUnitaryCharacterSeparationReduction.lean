import Langlands.TraceFormula.ArchimedeanUnitaryCharacterSeparationReductionStatement
import Langlands.TraceFormula.ArchimedeanCharacterKernels
import Langlands.TraceFormula.HilbertSumIntertwinerDominationProof
import Langlands.Analysis.OperatorTraceProof
import Langlands.Representation.Archimedean.HilbertIntertwinerEvaluation
import Langlands.Representation.Archimedean.UnitaryCommutant
import Langlands.Representation.Archimedean.UnitaryRegularization
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-! # Character separation given the archimedean trace-class theorem -/

noncomputable section

open MeasureTheory Set
open scoped ENNReal InnerProductSpace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe uF uι uH uE uκ

namespace Langlands.TraceFormula

open Langlands.Global Langlands.Global.ArchimedeanGL Langlands.Analysis.OperatorIdeals
open ArchimedeanUnitary

section IrreducibleIntertwiners

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}
  {D : Type uH} [NormedAddCommGroup D] [InnerProductSpace ℂ D] [CompleteSpace D]
  {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  {σ : InfiniteAdelicGL F n →* (D →L[ℂ] D)} {π : InfiniteAdelicGL F n →* (E →L[ℂ] E)}

omit [NumberField F] in
private theorem zero_of_inequivalent (hσ : IsIrreducibleUnitaryRepresentation σ)
    (hπ : IsIrreducibleUnitaryRepresentation π) (hne : ¬ UnitarilyEquivalent σ π)
    (T : D →L[ℂ] E) (hT : ∀ g x, T (σ g x) = π g (T x)) : T = 0 := by
  by_contra hTne
  let : Nontrivial D := hσ.2.1
  have hAdj (g : InfiniteAdelicGL F n) (x : E) : T.adjoint (π g x) = σ g (T.adjoint x) :=
    Archimedean.adjoint_mem_boundedIntertwiners σ π hσ.1.2 hπ.1.2 ⟨T, hT⟩ g x
  obtain ⟨a, ha⟩ := Archimedean.exists_eq_scalar_of_unitary_commute σ hσ.1.2 hσ.2
    (T.adjoint.comp T) (fun g => ContinuousLinearMap.ext fun x => by
      change T.adjoint (T (σ g x)) = σ g (T.adjoint (T x))
      rw [hT, hAdj])
  have haNorm : ‖a‖ = ‖T‖ ^ 2 := by
    simpa only [ha, norm_smul, ContinuousLinearMap.norm_id, mul_one, pow_two]
      using T.norm_adjoint_comp_self
  have hnorm (x : D) : ‖T x‖ = ‖T‖ * ‖x‖ := by
    have hinner : ⟪T x, T x⟫_ℂ = a * ⟪x, x⟫_ℂ := by
      rw [← T.adjoint_inner_right]
      change ⟪x, (T.adjoint.comp T) x⟫_ℂ = _
      rw [ha, smul_apply, ContinuousLinearMap.id_apply, inner_smul_right]
    apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
    simpa only [inner_self_eq_norm_sq_to_K, norm_mul, norm_pow, RCLike.norm_ofReal,
      abs_norm, haNorm, mul_pow] using congrArg norm hinner
  let s : ℂ := (‖T‖⁻¹ : ℝ)
  have hs : ‖s‖ = ‖T‖⁻¹ :=
    (Complex.norm_real _).trans (Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg T)))
  let e₀ : D →ₗᵢ[ℂ] E :=
    { toLinearMap := s • T.toLinearMap
      norm_map' := fun x => by
        change ‖s • T x‖ = ‖x‖
        rw [norm_smul, hs, hnorm, ← mul_assoc, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hTne), one_mul] }
  have he₀ (g : InfiniteAdelicGL F n) (x : D) : e₀ (σ g x) = π g (e₀ x) := by
    change s • T (σ g x) = π g (s • T x)
    rw [hT, map_smul]
  have hclosed : IsClosed (e₀.toLinearMap.range : Set E) :=
    e₀.isometry.isUniformInducing.isComplete_range.isClosed
  have hstable : ∀ g, ∀ x ∈ e₀.toLinearMap.range, π g x ∈ e₀.toLinearMap.range := by
    rintro g _ ⟨x, rfl⟩
    exact ⟨σ g x, he₀ g x⟩
  rcases hπ.2.2 e₀.toLinearMap.range hclosed hstable with hb | ht
  · obtain ⟨x, hx⟩ := exists_ne (0 : D)
    have hx' : e₀ x ∈ e₀.toLinearMap.range := ⟨x, rfl⟩
    rw [hb, Submodule.mem_bot] at hx'
    exact hx (e₀.injective (hx'.trans e₀.map_zero.symm))
  · exact hne ⟨LinearIsometryEquiv.ofSurjective e₀ (LinearMap.range_eq_top.mp ht), he₀⟩

variable [MeasurableSpace (InfiniteAdelicGL F n)] [BorelSpace (InfiniteAdelicGL F n)]
  {μ : Measure (InfiniteAdelicGL F n)} [μ.IsHaarMeasure]
  {A : SmoothCompactKernel F n → (D →L[ℂ] D)} {B : SmoothCompactKernel F n → (E →L[ℂ] E)}

private theorem trace_eq_of_equivalent (hσ : IsUnitaryRepresentation σ)
    (hA : ∀ f, IsIntegratedOperator μ σ f (A f))
    (hB : ∀ f, IsIntegratedOperator μ π f (B f)) (hEq : UnitarilyEquivalent σ π)
    (f : SmoothCompactKernel F n) (hTrace : IsTraceClass (A f)) :
    operatorTrace (A f) = operatorTrace (B f) := by
  obtain ⟨e, he⟩ := hEq
  let S := e.toContinuousLinearEquiv.toContinuousLinearMap
  let U := e.symm.toContinuousLinearEquiv.toContinuousLinearMap
  have h₁ : (S.comp (A f)).comp U = B f := by
    ext x
    change e (A f (e.symm x)) = B f x
    rw [show e (A f (e.symm x)) = B f (e (e.symm x)) from
      map_integrated_apply μ hσ hA hB S he f (e.symm x), e.apply_symm_apply]
  have h₂ : (A f).comp (U.comp S) = A f := by
    ext x
    change A f (e.symm (e x)) = A f x
    rw [e.symm_apply_apply]
  simpa only [h₁, h₂] using (operatorTraceCyclicity D E (A f) S U hTrace).2.2.symm

end IrreducibleIntertwiners

private theorem trace_adjoint_comp_self
    {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {κ : Type uκ} (b : HilbertBasis κ ℂ E) (T : E →L[ℂ] E)
    (ht : IsTraceClass (T.adjoint.comp T)) :
    Summable (fun i => ‖T (b i)‖ ^ 2) ∧
      operatorTrace (T.adjoint.comp T) = ((∑' i, ‖T (b i)‖ ^ 2 : ℝ) : ℂ) := by
  have hdiag (i : κ) : ⟪b i, (T.adjoint.comp T) (b i)⟫_ℂ = (‖T (b i)‖ ^ 2 : ℝ) := by
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_right,
      inner_self_eq_norm_sq_to_K, Complex.ofReal_pow]
    rfl
  have hnonneg (i : κ) : 0 ≤ ‖T (b i)‖ ^ 2 := sq_nonneg _
  obtain ⟨hs, ht'⟩ := operatorTraceBasis E _ κ b ht
  simp only [hdiag, Complex.norm_real, Real.norm_of_nonneg (hnonneg _)] at hs
  refine ⟨hs, ?_⟩
  rw [ht', traceIn, Complex.ofReal_tsum]
  exact tsum_congr hdiag

private theorem integrated_traceClass
    (htrace : ArchimedeanUnitaryTraceClassStatement.{uF, uE})
    {F : Type uF} [Field F] [NumberField F] {n : ℕ}
    [MeasurableSpace (InfiniteAdelicGL F n)] [BorelSpace (InfiniteAdelicGL F n)]
    (μ : Measure (InfiniteAdelicGL F n)) [μ.IsHaarMeasure]
    {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {π : InfiniteAdelicGL F n →* (E →L[ℂ] E)} (hπ : IsIrreducibleUnitaryRepresentation π)
    {A : SmoothCompactKernel F n → (E →L[ℂ] E)}
    (hA : ∀ f, IsIntegratedOperator μ π f (A f)) (f : SmoothCompactKernel F n) :
    IsTraceClass (A f) := by
  obtain ⟨B, hB, hBt⟩ := htrace F n μ E π hπ f
  have he : A f = B := ContinuousLinearMap.ext fun x => (hA f x).trans (hB x).symm
  rwa [he]

/-- The archimedean trace-class theorem implies separation of summable unitary characters. -/
theorem archimedeanUnitaryCharacterSeparation_of_traceClass :
    ArchimedeanUnitaryCharacterSeparationReductionStatement.{uF, uι, uH, uE} := by
  classical
  intro htraceH htraceE F _ _ n _ _ μ _ ι H _ _ _ σ A E _ _ _ π B c c₀ hσ hA hπ hB hsum
  let J : Set ι := {i | UnitarilyEquivalent (σ i) π}
  let Test := SmoothCompactKernel F n
  have htA (i : ι) (f : Test) : IsTraceClass (A i f) :=
    integrated_traceClass htraceH μ (hσ i) (hA i) f
  have htB (f : Test) : IsTraceClass (B f) := integrated_traceClass htraceE μ hπ hB f
  obtain ⟨κ, b, -⟩ := exists_hilbertBasis ℂ E
  let : Nontrivial E := hπ.2.1
  obtain ⟨y, hy⟩ := exists_ne (0 : E)
  have hκ : ∃ j : κ, b.repr y j ≠ 0 := by
    by_contra! h
    apply hy
    apply b.repr.injective
    rw [map_zero]
    exact lp.ext (funext h)
  obtain ⟨j, -⟩ := hκ
  have hx : b j ≠ 0 := (norm_pos_iff.mp (by rw [b.orthonormal.norm_eq_one j]; exact zero_lt_one))
  obtain ⟨f₀, hf₀⟩ := exists_integrated_ne_zero μ hπ.1 hB hx
  have htBsq (f : Test) : Summable (fun k => ‖B f (b k)‖ ^ 2) ∧
      operatorTrace (B (correlation μ f)) = ((∑' k, ‖B f (b k)‖ ^ 2 : ℝ) : ℂ) := by
    have ha := htB (correlation μ f)
    rw [integrated_correlation μ hπ.1 hB] at ha ⊢
    exact trace_adjoint_comp_self b _ ha
  have htest : operatorTrace (B (correlation μ f₀)) ≠ 0 := by
    rw [(htBsq f₀).2]
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt (lt_of_lt_of_le
      (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hf₀))
      ((htBsq f₀).1.le_tsum j (fun k _ => sq_nonneg ‖B f₀ (b k)‖))))
  have hEq (i : J) (f : Test) : operatorTrace (A i.val f) = operatorTrace (B f) :=
    trace_eq_of_equivalent (hσ i.val).1 (hA i.val) hB i.property f (htA i.val f)
  have hcJ : Summable (fun i : J => c i.val) := by
    let f := correlation μ f₀
    have hs := (hsum f).summable.subtype (· ∈ J)
    change Summable (fun i : J => c i.val * operatorTrace (A i.val f)) at hs
    simp_rw [hEq] at hs
    have hf : operatorTrace (B f) ≠ 0 := htest
    simpa only [mul_assoc, mul_inv_cancel₀ hf, mul_one] using
      hs.mul_right (operatorTrace (B f))⁻¹
  let C := ∑' i : J, c i.val
  let d := c₀ - C
  have hsum_compl (f : Test) :
      HasSum (fun i : ↥(Jᶜ) => c i.val * operatorTrace (A i.val f)) (d * operatorTrace (B f)) := by
    have hs := (hsum f).summable
    have hpart := hs.tsum_subtype_add_tsum_subtype_compl J
    have heq : (∑' i : J, c i.val * operatorTrace (A i.val f)) = C * operatorTrace (B f) := by
      simp_rw [hEq]
      rw [tsum_mul_right]
    rw [heq, (hsum f).tsum_eq] at hpart
    have hdiff : (∑' i : ↥(Jᶜ), c i.val * operatorTrace (A i.val f)) = d * operatorTrace (B f) := by
      calc
        _ = c₀ * operatorTrace (B f) - C * operatorTrace (B f) := eq_sub_of_add_eq' hpart
        _ = _ := (sub_mul _ _ _).symm
    rw [← hdiff]
    exact (hs.subtype (· ∈ Jᶜ)).hasSum
  have hd : d = 0 := by
    by_contra hdn
    choose s basis _ using fun i => exists_hilbertBasis ℂ (H i)
    have htAsq (i : ι) (f : Test) : Summable (fun k => ‖A i f (basis i k)‖ ^ 2) ∧
        operatorTrace (A i (correlation μ f)) = ((∑' k, ‖A i f (basis i k)‖ ^ 2 : ℝ) : ℂ) := by
      have ha := htA i (correlation μ f)
      rw [integrated_correlation μ (hσ i).1 (hA i)] at ha ⊢
      exact trace_adjoint_comp_self (basis i) _ ha
    let I := Σ i : ↥(Jᶜ), s i.val
    let W : I → Type uH := fun i => H i.1.val
    let LA (i : ι) := integratedLinearMap μ (hσ i).1 (hA i)
    let LB := integratedLinearMap μ hπ.1 hB
    let q (f : Test) (i : I) : W i :=
      (Real.sqrt ‖c i.1.val‖ : ℂ) • LA i.1.val f (basis i.1.val i.2)
    have hqnorm (f : Test) (i : I) :
        ‖q f i‖ ^ 2 = ‖c i.1.val‖ * ‖A i.1.val f (basis i.1.val i.2)‖ ^ 2 := by
      change ‖(Real.sqrt ‖c i.1.val‖ : ℂ) • A i.1.val f (basis i.1.val i.2)‖ ^ 2 = _
      rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow,
        Real.sq_sqrt (norm_nonneg _)]
    have hrow (f : Test) (i : ↥(Jᶜ)) :
        (∑' k, ‖q f ⟨i, k⟩‖ ^ 2) = ‖c i.val * operatorTrace (A i.val (correlation μ f))‖ := by
      simp_rw [hqnorm]
      rw [tsum_mul_left, (htAsq i.val f).2, norm_mul, Complex.norm_real, Real.norm_of_nonneg]
      exact tsum_nonneg fun k => sq_nonneg _
    have hsum_norm (f : Test) := summable_norm_iff.mpr (hsum_compl (correlation μ f)).summable
    have hrows (f : Test) (i : ↥(Jᶜ)) : Summable (fun k => ‖q f ⟨i, k⟩‖ ^ 2) := by
      simp_rw [hqnorm]
      exact (htAsq i.val f).1.mul_left ‖c i.val‖
    have hqsum (f : Test) : Summable (fun i => ‖q f i‖ ^ 2) := by
      apply (summable_sigma_of_nonneg fun i => sq_nonneg ‖q f i‖).2
      refine ⟨hrows f, ?_⟩
      simpa only [hrow] using hsum_norm f
    let v : Test →ₗ[ℂ] lp W 2 :=
      { toFun f := ⟨q f, memℓp_gen (by simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hqsum f)⟩
        map_add' f g := lp.ext (funext fun i => by
          change q (f + g) i = q f i + q g i
          simp only [q, map_add, add_apply, smul_add])
        map_smul' a f := lp.ext (funext fun i => by
          change q (a • f) i = a • q f i
          simp only [q, map_smul, smul_apply, smul_comm _ a]) }
    let w : Test →ₗ[ℂ] E :=
      { toFun f := LB f (b j)
        map_add' f g := by rw [map_add, add_apply]
        map_smul' a f := by rw [map_smul, smul_apply, RingHom.id_apply] }
    have hnorm (f : Test) : ‖v f‖ ^ 2 = ∑' i : ↥(Jᶜ), ‖c i.val * operatorTrace (A i.val (correlation μ f))‖ := by
      have h := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (v f)
      simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h
      rw [h]
      change (∑' i, ‖q f i‖ ^ (2 : ℕ)) = _
      exact ((hqsum f).tsum_sigma' (hrows f)).trans (tsum_congr (hrow f))
    have hBnorm (f : Test) : ‖w f‖ ^ 2 ≤ ‖operatorTrace (B (correlation μ f))‖ := by
      rw [(htBsq f).2, Complex.norm_real, Real.norm_of_nonneg (tsum_nonneg fun k => sq_nonneg ‖B f (b k)‖)]
      exact (htBsq f).1.le_tsum j (fun k _ => sq_nonneg ‖B f (b k)‖)
    have hdom (f : Test) : ‖d‖ * ‖w f‖ ^ 2 ≤ ‖v f‖ ^ 2 := calc
      _ ≤ ‖d * operatorTrace (B (correlation μ f))‖ := by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hBnorm f) (norm_nonneg _)
      _ ≤ _ := by
        rw [← (hsum_compl (correlation μ f)).tsum_eq, hnorm]
        exact norm_tsum_le_tsum_norm (hsum_norm f)
    have hspos : 0 < Real.sqrt ‖d‖ := Real.sqrt_pos_of_pos (norm_pos_iff.mpr hdn)
    have hbound (f : Test) : ‖w f‖ ≤ (Real.sqrt ‖d‖)⁻¹ * ‖v f‖ := by
      have hsq : (Real.sqrt ‖d‖ * ‖w f‖) ^ 2 ≤ ‖v f‖ ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (norm_nonneg _)]
        exact hdom f
      have hle := (sq_le_sq₀ (mul_nonneg hspos.le (norm_nonneg _)) (norm_nonneg _)).mp hsq
      exact (le_inv_mul_iff₀ hspos).2 hle
    have hw : w = 0 := hilbertSumIntertwinerDomination
      (InfiniteAdelicGL F n) I W (fun i => σ i.1.val)
      (fun i => Archimedean.norm_apply_of_preserves_inner (σ i.1.val) (hσ i.1.val).1.2)
      E π (fun i T hT => zero_of_inequivalent (hσ i.1.val) hπ i.1.property T hT)
      Test v w (fun g f => ⟨leftTranslate g f, fun i => by
        change q (leftTranslate g f) i = σ i.1.val g (q f i)
        change (Real.sqrt ‖c i.1.val‖ : ℂ) • A i.1.val (leftTranslate g f) (basis i.1.val i.2) = _
        rw [integrated_leftTranslate μ (hσ i.1.val).1 (hA i.1.val), ← map_smul]
        rfl,
        integrated_leftTranslate μ hπ.1 hB g f (b j)⟩) ⟨_, hbound⟩
    exact hf₀ (congrArg (fun T : Test →ₗ[ℂ] E => T f₀) hw)
  have hC : C = c₀ := (sub_eq_zero.mp hd).symm
  refine ⟨hC ▸ hcJ.hasSum, fun hc₀ => ?_⟩
  by_contra! hnone
  have : IsEmpty J := ⟨fun i => hnone i.val i.property⟩
  exact hc₀ ((hC ▸ hcJ.hasSum : HasSum (fun i : J => c i.val) c₀).unique hasSum_empty)

end Langlands.TraceFormula
