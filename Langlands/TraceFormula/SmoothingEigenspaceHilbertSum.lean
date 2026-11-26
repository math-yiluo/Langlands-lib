import Langlands.TraceFormula.CompactOperatorTraceReplacement

/-! # Smoothing eigenspace traces along a Hilbert sum -/

noncomputable section

namespace Langlands.TraceFormula

open Langlands.Analysis.OperatorIdeals Module.End
open scoped InnerProductSpace

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private local instance {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
    (T : K →L[ℂ] K) (z : ℂ) : CompleteSpace (eigenspace T.toLinearMap z) :=
  (ContinuousLinearMap.isClosed_eigenspace T z).completeSpace_coe

/-- Orthogonal compression of a bounded operator to a complete submodule. -/
def summandCompression (W : Submodule ℂ H) [CompleteSpace W] (A : H →L[ℂ] H) :
    W →L[ℂ] W :=
  W.orthogonalProjectionOnto ∘L A ∘L W.subtypeL

omit [CompleteSpace H] in
/-- Orthogonal compression preserves symmetry. -/
theorem summandCompression_isSymmetric (W : Submodule ℂ H) [CompleteSpace W]
    (T : H →L[ℂ] H) (hT : T.IsSymmetric) : (summandCompression W T).IsSymmetric := by
  intro x y
  change ⟪summandCompression W T x, y⟫_ℂ = ⟪x, summandCompression W T y⟫_ℂ
  simpa [summandCompression] using hT (x : H) (y : H)

omit [CompleteSpace H] in
private theorem summandCompression_apply_of_mem (W : Submodule ℂ H) [CompleteSpace W]
    (T : H →L[ℂ] H) (hW : ∀ x ∈ W, T x ∈ W) (x : W) :
    (summandCompression W T x : H) = T x :=
  congrArg Subtype.val
    (W.orthogonalProjectionOnto_mem_subspace_eq_self ⟨T x, hW x x.2⟩)

omit [CompleteSpace H] in
/-- A right-hand power of an operator preserving `W` compresses to the same
power of its compression, also when preceded by an arbitrary bounded operator. -/
theorem summandCompression_mul_pow (W : Submodule ℂ H) [CompleteSpace W]
    (T A : H →L[ℂ] H) (hW : ∀ x ∈ W, T x ∈ W) (k : ℕ) :
    summandCompression W (A * T ^ k) = summandCompression W A * summandCompression W T ^ k := by
  have hPow (j : ℕ) (x : W) : ((summandCompression W T ^ j) x : H) = (T ^ j) x := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ', pow_succ', mul_apply_eq_comp, mul_apply_eq_comp,
        summandCompression_apply_of_mem W T hW, ih]
  ext1 x
  simp only [summandCompression, ContinuousLinearMap.comp_apply, Submodule.subtypeL_apply,
    mul_apply_eq_comp]
  rw [← hPow k x]
  rfl

omit [CompleteSpace H] in
private theorem starProjection_apply_operator (W : Submodule ℂ H) [CompleteSpace W]
    (T : H →L[ℂ] H) (hT : T.IsSymmetric) (hW : ∀ x ∈ W, T x ∈ W) (x : H) :
    W.starProjection (T x) = T (W.starProjection x) := by
  apply W.eq_starProjection_of_mem_of_inner_eq_zero (hW _ (W.starProjection_apply_mem x))
  intro y hy
  calc
    ⟪T x - T (W.starProjection x), y⟫_ℂ = ⟪T (x - W.starProjection x), y⟫_ℂ := by rw [map_sub]
    _ = ⟪x - W.starProjection x, T y⟫_ℂ := hT _ _
    _ = 0 := W.starProjection_inner_eq_zero x _ (hW y hy)

private def eigenspaceInter (T : H →L[ℂ] H) (z : ℂ) (W : Submodule ℂ H) :
    Submodule ℂ (eigenspace T.toLinearMap z) :=
  W.comap (eigenspace T.toLinearMap z).subtype

private local instance (T : H →L[ℂ] H) (z : ℂ) (W : Submodule ℂ H) [CompleteSpace W] :
    CompleteSpace (eigenspaceInter T z W) := by
  change CompleteSpace ((↑(eigenspace T.toLinearMap z).subtype) ⁻¹' (W : Set H))
  have hClosed : IsClosed (W : Set H) := (completeSpace_coe_iff_isComplete.mp ‹_›).isClosed
  exact (hClosed.preimage continuous_subtype_val).completeSpace_coe

private def summandEigenspaceEquiv (W : Submodule ℂ H) [CompleteSpace W] (T : H →L[ℂ] H)
    (hW : ∀ x ∈ W, T x ∈ W) (z : ℂ) :
    eigenspace (summandCompression W T).toLinearMap z ≃ₗᵢ[ℂ] eigenspaceInter T z W := by
  have hEig (x : W) : x ∈ eigenspace (summandCompression W T).toLinearMap z ↔
      (x : H) ∈ eigenspace T.toLinearMap z := by
    rw [mem_eigenspace_iff, mem_eigenspace_iff]
    change summandCompression W T x = z • x ↔ T x = z • (x : H)
    rw [← summandCompression_apply_of_mem W T hW x]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  let e : eigenspace (summandCompression W T).toLinearMap z →ₗᵢ[ℂ] eigenspaceInter T z W :=
    { toFun := fun x => ⟨⟨(x : W), (hEig x).1 x.2⟩, (x : W).2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      norm_map' := fun _ => rfl }
  refine LinearIsometryEquiv.ofSurjective e ?_
  intro x
  let y : W := ⟨(x : eigenspace T.toLinearMap z), x.2⟩
  exact ⟨⟨y, (hEig y).2 (x : eigenspace T.toLinearMap z).2⟩, rfl⟩

private theorem eigenspaceInter_trace (W : Submodule ℂ H) [CompleteSpace W]
    (T A : H →L[ℂ] H) (hW : ∀ x ∈ W, T x ∈ W) (z : ℂ)
    [FiniteDimensional ℂ (eigenspace T.toLinearMap z)] :
    operatorTrace (E := eigenspaceInter T z W) (summandCompression (eigenspaceInter T z W)
      (summandCompression (eigenspace T.toLinearMap z) A)) =
      eigenspaceTrace (summandCompression W T) z (summandCompression W A) := by
  let E := eigenspace T.toLinearMap z
  let V := eigenspace (summandCompression W T).toLinearMap z
  let P := eigenspaceInter T z W
  let e := summandEigenspaceEquiv W T hW z
  let : FiniteDimensional ℂ V := FiniteDimensional.of_injective e.toLinearMap e.injective
  let b := stdOrthonormalBasis ℂ V
  change operatorTrace (E := P) (summandCompression P (summandCompression E A)) =
    operatorTrace (E := V) (summandCompression V (summandCompression W A))
  rw [operatorTrace_eq_sum_diagonal (b.map e), operatorTrace_eq_sum_diagonal b]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [OrthonormalBasis.map_apply, summandCompression, inner_compression_apply]
  rw [inner_compression_apply E A (e (b j) : E)]
  rfl

/-- For a symmetric trace-class operator preserving every summand of a Hilbert sum,
each nonzero eigenspace trace is the sum of the corresponding traces on finitely
many summands. The same finite set works for every compressed operator. -/
def SmoothingEigenspaceHilbertSumStatement : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (ι : Type v) (W : ι → Submodule ℂ H) [∀ i, CompleteSpace (W i)],
    IsHilbertSum ℂ (fun i => W i) (fun i => (W i).subtypeₗᵢ) →
    ∀ T : H →L[ℂ] H, IsTraceClass T → T.IsSymmetric → (∀ i x, x ∈ W i → T x ∈ W i) →
    ∀ z : ℂ, z ≠ 0 → ∃ D : Finset ι, ∀ A : H →L[ℂ] H,
      eigenspaceTrace T z A = ∑ i ∈ D,
        eigenspaceTrace (summandCompression (W i) T) z (summandCompression (W i) A)

theorem smoothingEigenspaceHilbertSum : SmoothingEigenspaceHilbertSumStatement.{u, v} := by
  intro H _ _ _ ι W _ hW T hClass hSymm hInv z hz
  classical
  let E := eigenspace T.toLinearMap z
  let P := fun i => eigenspaceInter T z (W i)
  have hCompact := hilbertSchmidtCompact H H T (isHilbertSchmidt_of_isTraceClass T hClass)
  let : FiniteDimensional ℂ E := T.finite_dimensional_eigenspace hCompact z hz
  have hOrtho : OrthogonalFamily ℂ (fun i => P i) (fun i => (P i).subtypeₗᵢ) := by
    intro i j hij x y
    exact hW.OrthogonalFamily hij ⟨(x : E), x.2⟩ ⟨(y : E), y.2⟩
  have hTotal : (⨆ i, P i)ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    rw [Submodule.mem_orthogonal'] at hx
    have hZero (i : ι) : (W i).starProjection (x : H) = 0 := by
      let y := (W i).starProjection (x : H)
      have hy : y ∈ E := by
        rw [mem_eigenspace_iff]
        change T ((W i).starProjection x) = z • (W i).starProjection x
        rw [← starProjection_apply_operator (W i) T hSymm (hInv i),
          show T x = z • (x : H) from mem_eigenspace_iff.mp x.2, map_smul]
      have hyW : y ∈ W i := (W i).starProjection_apply_mem x
      let yE : E := ⟨y, hy⟩
      have hxy : ⟪(x : H), y⟫_ℂ = 0 := hx yE (le_iSup P i (show yE ∈ P i from hyW))
      apply (inner_self_eq_zero (𝕜 := ℂ)).mp
      calc
        ⟪y, y⟫_ℂ = ⟪(W i).starProjection (x : H), y⟫_ℂ := rfl
        _ = ⟪(x : H), (W i).starProjection y⟫_ℂ :=
          (W i).inner_starProjection_left_eq_right _ _
        _ = 0 := by rw [Submodule.starProjection_eq_self_iff.mpr hyW, hxy]
    have hSum := hW.hasSum_linearIsometryEquiv_symm (hW.linearIsometryEquiv (x : H))
    rw [LinearIsometryEquiv.symm_apply_apply] at hSum
    have hInnerSum := (innerSL ℂ (x : H)).hasSum hSum
    have hInnerZero (i : ι) (y : W i) : ⟪(x : H), (y : H)⟫_ℂ = 0 :=
      (Submodule.mem_orthogonal' _ _).mp ((W i).starProjection_apply_eq_zero_iff.mp (hZero i))
        y y.2
    exact Subtype.ext ((inner_self_eq_zero (𝕜 := ℂ)).mp
      ((hInnerSum.congr_fun fun i => (hInnerZero i _).symm).unique hasSum_zero))
  have hP : IsHilbertSum ℂ (fun i => P i) (fun i => (P i).subtypeₗᵢ) :=
    IsHilbertSum.mkInternal P hOrtho (Submodule.topologicalClosure_eq_top_iff.mpr hTotal).ge
  let I : Set ι := {i | P i ≠ ⊥}
  have hFinite : I.Finite := by
    choose x hx hne using fun i : I => Submodule.exists_mem_ne_zero_of_ne_bot i.2
    have hIndependent : LinearIndependent ℂ x :=
      linearIndependent_of_ne_zero_of_inner_eq_zero hne fun i j hij =>
        hOrtho (fun h => hij (Subtype.ext h)) ⟨x i, hx i⟩ ⟨x j, hx j⟩
    let : Finite I := hIndependent.finite
    exact Set.toFinite I
  refine ⟨hFinite.toFinset, fun A => ?_⟩
  let B := summandCompression E A
  let F := fun i => operatorTrace (E := P i) (summandCompression (P i) B)
  have hSum : HasSum F (eigenspaceTrace T z A) :=
    (hilbertSum_trace_hasSum P hP B (isTraceClass_of_finiteDimensional B)).2
  rw [← hSum.tsum_eq, tsum_eq_sum (s := hFinite.toFinset)]
  · exact Finset.sum_congr rfl fun i _ => eigenspaceInter_trace (W i) T A (hInv i) z
  · intro i hi
    have hBot : P i = ⊥ := by
      apply not_ne_iff.mp
      intro h
      apply hi
      rw [Set.Finite.mem_toFinset]
      exact h
    let : Subsingleton (P i) := Submodule.subsingleton_iff_eq_bot.mpr hBot
    have hZero : summandCompression (P i) B = 0 := by
      ext1 x
      exact Subsingleton.elim _ _
    change operatorTrace (E := P i) (summandCompression (P i) B) = 0
    rw [hZero, operatorTrace_zero]

end Langlands.TraceFormula
