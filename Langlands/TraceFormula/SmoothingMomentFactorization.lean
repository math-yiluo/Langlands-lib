import Langlands.TraceFormula.CompactOperatorTraceReplacement

/-! # Local trace factors on nonzero smoothing eigenspaces -/

noncomputable section

namespace Langlands.TraceFormula

open Langlands.Analysis.OperatorIdeals Module.End

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

private local instance (T : H →L[ℂ] H) (z : ℂ) : CompleteSpace (eigenspace T.toLinearMap z) :=
  (ContinuousLinearMap.isClosed_eigenspace T z).completeSpace_coe

private theorem eigenspaceTrace_zero (T : H →L[ℂ] H) (z : ℂ) :
    eigenspaceTrace T z 0 = 0 := by
  simp [eigenspaceTrace, operatorTrace_zero]

private theorem eigenspaceTrace_project (T A : H →L[ℂ] H) (hT : T.IsSymmetric) (z w : ℂ) :
    eigenspaceTrace T w ((eigenspace T.toLinearMap z).starProjection ∘L A) =
      if w = z then eigenspaceTrace T w A else 0 := by
  classical
  let W := fun s : ℂ => eigenspace T.toLinearMap s
  let P := (W z).starProjection
  change operatorTrace ((W w).orthogonalProjectionOnto ∘L (P ∘L A) ∘L (W w).subtypeL) = _
  by_cases hw : w = z
  · subst w
    rw [ite_eq_left rfl]
    congr 1
    ext1 x
    exact (W z).orthogonalProjectionOnto_mem_subspace_eq_self
      ((W z).orthogonalProjectionOnto (A x))
  · rw [ite_eq_right hw]
    have hZero : (W w).orthogonalProjectionOnto ∘L (P ∘L A) ∘L (W w).subtypeL = 0 := by
      ext1 x
      change (W w).orthogonalProjectionOnto (P (A x)) = 0
      rw [Submodule.orthogonalProjectionOnto_eq_zero_iff]
      exact Submodule.isOrtho_iff_le.mp (hT.orthogonalFamily_eigenspaces.isOrtho
        (fun h : z = w => hw h.symm))
        ((W z).starProjection_apply_mem (A x))
    rw [hZero, operatorTrace_zero]

private theorem operatorTrace_project_mul (T A : H →L[ℂ] H) (hT : IsTraceClass T)
    {z : ℂ} (hz : z ≠ 0) :
    operatorTrace (((eigenspace T.toLinearMap z).starProjection ∘L A) * T) =
      z * eigenspaceTrace T z A := by
  let W := eigenspace T.toLinearMap z
  have hCompact := hilbertSchmidtCompact H H T (isHilbertSchmidt_of_isTraceClass T hT)
  let : FiniteDimensional ℂ W := T.finite_dimensional_eigenspace hCompact z hz
  let C := W.orthogonalProjectionOnto ∘L A
  have hProduct : (W.starProjection ∘L A) * T = W.subtypeL ∘L (C ∘L T) := by
    ext1 x
    rfl
  have hCompress : (C ∘L T) ∘L W.subtypeL = z • (C ∘L W.subtypeL) := by
    ext1 x
    have hx : T x = z • (x : H) := mem_eigenspace_iff.mp x.property
    simp [hx]
  rw [hProduct, (operatorTrace_finite_compression W.subtypeL (C ∘L T)).2,
    hCompress, operatorTrace_smul _ _ (isTraceClass_of_finiteDimensional _)]
  rfl

/-- Vanishing of all positive-power traces gives vanishing of the trace compressed
to each nonzero eigenspace of the smoothing operator. -/
theorem eigenspaceTrace_eq_zero_of_power_traces (T A : H →L[ℂ] H)
    (hT : IsTraceClass T) (hSymm : T.IsSymmetric)
    (hPowers : ∀ k : ℕ, operatorTrace (A * T ^ (k + 1)) = 0) {z : ℂ} (hz : z ≠ 0) :
    eigenspaceTrace T z A = 0 := by
  let B := (eigenspace T.toLinearMap z).starProjection ∘L A
  have hTrace := compactOperatorTraceReplacement H H T T Unit (fun _ => A) (fun _ => 0)
    B 0 hT hT hSymm hSymm
    (fun _ k => by simpa only [zero_mul, operatorTrace_zero] using hPowers k)
    (fun w _ hEq => by
      classical
      rw [eigenspaceTrace_zero] at hEq ⊢
      rw [show B = _ from rfl, eigenspaceTrace_project T A hSymm, hEq ()]
      simp)
  rw [zero_mul, operatorTrace_zero] at hTrace
  have hZero : z * eigenspaceTrace T z A = 0 :=
    (operatorTrace_project_mul T A hT hz).symm.trans hTrace
  exact (mul_eq_zero.mp hZero).resolve_left hz

private theorem operatorTrace_sub_smul (A B : H →L[ℂ] H) (c : ℂ)
    (hA : IsTraceClass A) (hB : IsTraceClass B) :
    operatorTrace (A - c • B) = operatorTrace A - c * operatorTrace B := by
  rw [sub_eq_add_neg, ← neg_smul, operatorTrace_add _ _ hA (isTraceClass_smul _ _ hB),
    operatorTrace_smul _ _ hB, neg_mul, ← sub_eq_add_neg]

private theorem eigenspaceTrace_sub_smul (T A B : H →L[ℂ] H) (hT : IsTraceClass T)
    {z : ℂ} (hz : z ≠ 0) (c : ℂ) :
    eigenspaceTrace T z (A - c • B) =
      eigenspaceTrace T z A - c * eigenspaceTrace T z B := by
  let W := eigenspace T.toLinearMap z
  have hCompact := hilbertSchmidtCompact H H T (isHilbertSchmidt_of_isTraceClass T hT)
  let : FiniteDimensional ℂ W := T.finite_dimensional_eigenspace hCompact z hz
  change operatorTrace (W.orthogonalProjectionOnto ∘L (A - c • B) ∘L W.subtypeL) = _
  have hMap : W.orthogonalProjectionOnto ∘L (A - c • B) ∘L W.subtypeL =
      (W.orthogonalProjectionOnto ∘L A ∘L W.subtypeL) -
        c • (W.orthogonalProjectionOnto ∘L B ∘L W.subtypeL) := by
    ext1 x
    simp
  rw [hMap, operatorTrace_sub_smul _ _ _ (isTraceClass_of_finiteDimensional _)
    (isTraceClass_of_finiteDimensional _)]
  rfl

/-- If all positive-power trace functionals share one factor in the test
variable, every nonzero eigenspace compression shares the same factor. -/
def SmoothingMomentFactorizationStatement : Prop :=
  ∀ (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : H →L[ℂ] H) (ι : Type v) (A : ι → H →L[ℂ] H) (L : ι → ℂ) (C : ℕ → ℂ),
    IsTraceClass T → T.IsSymmetric →
    (∀ i k, operatorTrace (A i * T ^ (k + 1)) = L i * C k) →
    ∀ z : ℂ, z ≠ 0 → ∃ c : ℂ, ∀ i, eigenspaceTrace T z (A i) = L i * c

theorem smoothingMomentFactorization : SmoothingMomentFactorizationStatement.{u, v} := by
  intro H _ _ _ T ι A L C hT hSymm hPowers z hz
  classical
  by_cases hL : ∃ i, L i ≠ 0
  · obtain ⟨i₀, hi₀⟩ := hL
    refine ⟨eigenspaceTrace T z (A i₀) / L i₀, fun i => ?_⟩
    let c := L i / L i₀
    have hZero (k : ℕ) : operatorTrace ((A i - c • A i₀) * T ^ (k + 1)) = 0 := by
      have hClass (j : ι) : IsTraceClass (A j * T ^ (k + 1)) := by
        rw [pow_succ, ← mul_assoc]
        exact isTraceClass_postcomp T (A j * T ^ k) hT
      rw [sub_mul, smul_mul_assoc, operatorTrace_sub_smul _ _ _ (hClass i) (hClass i₀),
        hPowers i, hPowers i₀]
      rw [← mul_assoc, div_mul_cancel₀ _ hi₀, sub_self]
    have h := eigenspaceTrace_eq_zero_of_power_traces T (A i - c • A i₀) hT hSymm hZero hz
    rw [eigenspaceTrace_sub_smul _ _ _ hT hz] at h
    rw [sub_eq_zero.mp h]
    dsimp [c]
    ring
  · push Not at hL
    refine ⟨0, fun i => ?_⟩
    rw [mul_zero]
    exact eigenspaceTrace_eq_zero_of_power_traces T (A i) hT hSymm
      (fun k => by rw [hPowers i k, hL i, zero_mul]) hz

end Langlands.TraceFormula
