import Langlands.Analysis.HilbertSumTraceStatement
import Langlands.Analysis.OperatorTraceProof

/-!
# Traces of trace-class operators along closed subspaces and Hilbert sums: proof

This module proves `HilbertSumTraceStatement`.

* For a complete subspace `S` containing the range of a trace-class `B`, the compression
  `P_S ∘ B ∘ ι_S` is trace class with trace `tr B`, by bounded rectangular cyclicity applied
  twice.
* For a Hilbert sum `E = ⨁ W i`, Hilbert bases of the summands combine into a Hilbert basis of
  `E` indexed by a sigma type; the basis formula for `tr B` in that basis is grouped by summand,
  and each group is the basis formula for the trace of the compression to `W i`.
* If `B` maps `W i` into `W (τ i)`, the compression to `W i` vanishes for `τ i ≠ i`.
-/

noncomputable section

namespace Langlands.Analysis.OperatorIdeals

universe u v w

section Compression

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The compression `P_W ∘ B ∘ ι_W` of a trace-class operator to a complete subspace is trace
class. -/
theorem isTraceClass_compression (W : Submodule ℂ E) [CompleteSpace W] (B : E →L[ℂ] E)
    (hB : IsTraceClass B) :
    IsTraceClass (W.orthogonalProjectionOnto ∘L B ∘L W.subtypeL) := by
  have h := (operatorTraceCyclicity.{u, u} E W B W.orthogonalProjectionOnto W.subtypeL hB).1
  rwa [ContinuousLinearMap.comp_assoc] at h

/-- Part 1: compression to a complete subspace containing the range of `B`. -/
theorem compression_trace_of_range (S : Submodule ℂ E) [CompleteSpace S] (B : E →L[ℂ] E)
    (hB : IsTraceClass B) (hS : ∀ x, B x ∈ S) :
    IsTraceClass (S.orthogonalProjectionOnto ∘L B ∘L S.subtypeL) ∧
      operatorTrace (S.orthogonalProjectionOnto ∘L B ∘L S.subtypeL) = operatorTrace B := by
  obtain ⟨-, -, h2⟩ :=
    operatorTraceCyclicity.{u, u} E S B S.orthogonalProjectionOnto S.subtypeL hB
  -- `Q = ι_S ∘ P_S` is the orthogonal projection of `E` onto `S`, and `Q ∘ B = B`.
  have hQB : (S.subtypeL ∘L S.orthogonalProjectionOnto) ∘L B = B := by
    ext x
    exact congrArg Subtype.val
      (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (K := S) ⟨B x, hS x⟩)
  obtain ⟨-, -, h3⟩ := operatorTraceCyclicity.{u, u} E E B
    (S.subtypeL ∘L S.orthogonalProjectionOnto) (ContinuousLinearMap.id ℂ E) hB
  rw [ContinuousLinearMap.comp_id, hQB, ContinuousLinearMap.id_comp] at h3
  refine ⟨isTraceClass_compression S B hB, ?_⟩
  rw [← ContinuousLinearMap.comp_assoc, h2]
  exact h3.symm

omit [CompleteSpace E] in
/-- The diagonal coefficients of a compression are those of the operator. -/
theorem inner_compression_apply (W : Submodule ℂ E) [CompleteSpace W] (B : E →L[ℂ] E)
    (x : W) :
    inner ℂ x ((W.orthogonalProjectionOnto ∘L B ∘L W.subtypeL) x) = inner ℂ (x : E) (B x) := by
  simp

/-- The basis formula for the trace of a compression, written with the diagonal coefficients
of the operator itself. -/
theorem hasSum_inner_compression (W : Submodule ℂ E) [CompleteSpace W] (B : E →L[ℂ] E)
    (hB : IsTraceClass B) {κ : Type w} (b : HilbertBasis κ ℂ W) :
    Summable (fun k => ‖inner ℂ ((b k : W) : E) (B (b k))‖) ∧
      HasSum (fun k => inner ℂ ((b k : W) : E) (B (b k)))
        (operatorTrace (W.orthogonalProjectionOnto ∘L B ∘L W.subtypeL)) := by
  obtain ⟨hs, htr⟩ := operatorTraceBasis.{u, w} W
    (W.orthogonalProjectionOnto ∘L B ∘L W.subtypeL) κ b (isTraceClass_compression W B hB)
  simp only [inner_compression_apply] at hs
  refine ⟨hs, ?_⟩
  rw [htr, traceIn]
  simp only [inner_compression_apply]
  exact (Summable.of_norm hs).hasSum

end Compression

section HilbertSum

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Hilbert bases of the summands of a Hilbert sum span a dense subspace: the orthogonal
complement of the span of the combined family is zero. -/
theorem orthogonal_span_sigma_eq_bot {ι : Type v} (W : ι → Submodule ℂ E)
    [∀ i, CompleteSpace (W i)]
    (hW : IsHilbertSum ℂ (fun i => W i) (fun i => (W i).subtypeₗᵢ))
    {κ : ι → Type w} (b : ∀ i, HilbertBasis (κ i) ℂ (W i)) :
    (Submodule.span ℂ
        (Set.range fun a : Σ i, κ i => (W a.1).subtypeₗᵢ (b a.1 a.2)))ᗮ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  rw [Submodule.mem_orthogonal'] at hx
  -- `x` is orthogonal to every summand.
  have h1 : ∀ i, ∀ y : W i, inner ℂ x (y : E) = 0 := by
    intro i y
    let φ : W i →L[ℂ] ℂ := (innerSL ℂ x).comp (W i).subtypeL
    have hker : (Submodule.span ℂ (Set.range (b i))).topologicalClosure ≤ φ.ker := by
      refine Submodule.topologicalClosure_minimal _ ?_ φ.isClosed_ker
      rw [Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      exact hx _ (Submodule.subset_span ⟨⟨i, k⟩, rfl⟩)
    rw [(b i).dense_span] at hker
    exact hker (Submodule.mem_top (x := y))
  -- Expand `x` along the Hilbert sum.
  have hsum := hW.hasSum_linearIsometryEquiv_symm (hW.linearIsometryEquiv x)
  rw [LinearIsometryEquiv.symm_apply_apply] at hsum
  have h2 := (innerSL ℂ x).hasSum hsum
  have h3 : (fun i => innerSL ℂ x ((W i).subtypeₗᵢ (hW.linearIsometryEquiv x i))) = 0 := by
    funext i
    exact h1 i _
  rw [h3] at h2
  exact inner_self_eq_zero.mp (h2.unique hasSum_zero)

/-- Part 2 (without the twisted clause): the compressions to the summands of a Hilbert sum are
trace class, their traces are absolutely summable, and their sum is the trace. -/
theorem hilbertSum_trace_hasSum {ι : Type v} (W : ι → Submodule ℂ E)
    [∀ i, CompleteSpace (W i)]
    (hW : IsHilbertSum ℂ (fun i => W i) (fun i => (W i).subtypeₗᵢ))
    (B : E →L[ℂ] E) (hB : IsTraceClass B) :
    Summable (fun i =>
        ‖operatorTrace ((W i).orthogonalProjectionOnto ∘L B ∘L (W i).subtypeL)‖) ∧
      HasSum (fun i => operatorTrace ((W i).orthogonalProjectionOnto ∘L B ∘L (W i).subtypeL))
        (operatorTrace B) := by
  choose s b _ using fun i => exists_hilbertBasis ℂ (W i)
  let e : (Σ i, s i) → E := fun a => (W a.1).subtypeₗᵢ (b a.1 a.2)
  have he : Orthonormal ℂ e :=
    hW.OrthogonalFamily.orthonormal_sigma_orthonormal fun i => (b i).orthonormal
  let bE : HilbertBasis (Σ i, s i) ℂ E :=
    HilbertBasis.mkOfOrthogonalEqBot he (orthogonal_span_sigma_eq_bot W hW b)
  have hbE : ⇑bE = e := HilbertBasis.coe_mkOfOrthogonalEqBot he _
  obtain ⟨hnorm, htr⟩ := operatorTraceBasis E B (Σ i, s i) bE hB
  rw [hbE] at hnorm
  rw [traceIn, hbE] at htr
  have hall : HasSum (fun a => inner ℂ (e a) (B (e a))) (operatorTrace B) := by
    rw [htr]
    exact (Summable.of_norm hnorm).hasSum
  have hpart := fun i => hasSum_inner_compression (W i) B hB (b i)
  refine ⟨?_, hall.sigma fun i => (hpart i).2⟩
  refine Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => ?_) hnorm.sigma
  rw [← (hpart i).2.tsum_eq]
  exact norm_tsum_le_tsum_norm (hpart i).1

/-- The twisted clause: if `B` maps `W i` into `W (τ i)`, the compression to `W i` is zero
unless `τ i = i`. -/
theorem compression_eq_zero_of_ne {ι : Type v} (W : ι → Submodule ℂ E)
    [∀ i, CompleteSpace (W i)]
    (hW : IsHilbertSum ℂ (fun i => W i) (fun i => (W i).subtypeₗᵢ))
    (B : E →L[ℂ] E) (τ : ι → ι) (hτ : ∀ i, ∀ x ∈ W i, B x ∈ W (τ i)) (i : ι) (hi : τ i ≠ i) :
    (W i).orthogonalProjectionOnto ∘L B ∘L (W i).subtypeL = 0 := by
  ext1 x
  show (W i).orthogonalProjectionOnto (B x) = 0
  rw [Submodule.orthogonalProjectionOnto_eq_zero_iff]
  exact Submodule.isOrtho_iff_le.mp (hW.OrthogonalFamily.isOrtho hi) (hτ i x x.2)

end HilbertSum

/-- **Traces along subspaces and Hilbert sums.** -/
theorem hilbertSumTrace : HilbertSumTraceStatement.{u, v} := by
  refine ⟨fun E _ _ _ S _ B hB hS => compression_trace_of_range S B hB hS, ?_⟩
  intro E _ _ _ ι W _ hW B hB
  obtain ⟨hsum, hhas⟩ := hilbertSum_trace_hasSum W hW B hB
  refine ⟨fun i => isTraceClass_compression (W i) B hB, hsum, hhas, ?_⟩
  intro τ hτ
  have hsupp : Function.support
      (fun i => operatorTrace ((W i).orthogonalProjectionOnto ∘L B ∘L (W i).subtypeL)) ⊆
        {i | τ i = i} := by
    intro i hi
    by_contra hne
    apply hi
    simp only
    rw [compression_eq_zero_of_ne W hW B τ hτ i hne, operatorTrace_zero]
  exact (hasSum_subtype_iff_of_support_subset hsupp).mpr hhas

end Langlands.Analysis.OperatorIdeals
