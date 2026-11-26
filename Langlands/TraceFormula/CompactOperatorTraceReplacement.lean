import Langlands.Analysis.HilbertSchmidtCompactProof
import Langlands.Analysis.HilbertSumTraceProof
import Langlands.Analysis.OperatorTraceFiniteCompression
import Langlands.Analysis.TraceClassHilbertSchmidtProof
import Langlands.Analysis.TraceClassIdealProof
import Langlands.TraceFormula.BoundedCharacterSeparationProof
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.LinearAlgebra.Eigenspace.ContinuousLinearMap
import Mathlib.Topology.Algebra.Polynomial

/-! # Trace replacement by compact self-adjoint smoothing -/

noncomputable section

namespace Langlands.TraceFormula

open Langlands.Analysis.OperatorIdeals Module.End

universe u v w

section OneSpace

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance (T : H →L[ℂ] H) (z : ℂ) : CompleteSpace (eigenspace T.toLinearMap z) :=
  (ContinuousLinearMap.isClosed_eigenspace T z).completeSpace_coe

/-- The trace of the orthogonal compression of `A` to the `z`-eigenspace of `T`. -/
def eigenspaceTrace (T : H →L[ℂ] H) (z : ℂ) (A : H →L[ℂ] H) : ℂ :=
  let W := eigenspace T.toLinearMap z
  operatorTrace (W.orthogonalProjectionOnto ∘L A ∘L W.subtypeL)

private theorem eigenspaceTrace_eq_zero_of_not_hasEigenvalue (T : H →L[ℂ] H)
    (z : ℂ) (A : H →L[ℂ] H) (hz : ¬ HasEigenvalue T.toLinearMap z) :
    eigenspaceTrace T z A = 0 := by
  let W := eigenspace T.toLinearMap z
  have hW : W = ⊥ := not_ne_iff.mp (mt (hasEigenvalue_iff.mpr) hz)
  let : Subsingleton W := Submodule.subsingleton_iff_eq_bot.mpr hW
  have hmap : W.orthogonalProjectionOnto ∘L A ∘L W.subtypeL = 0 := by
    ext1 x
    exact Subsingleton.elim _ _
  change operatorTrace (W.orthogonalProjectionOnto ∘L A ∘L W.subtypeL) = 0
  rw [hmap, operatorTrace_zero]

omit [CompleteSpace H] in
private theorem hasEigenvalue_norm_le (T : H →L[ℂ] H) {z : ℂ}
    (hz : HasEigenvalue T.toLinearMap z) : ‖z‖ ≤ ‖T‖ := by
  obtain ⟨x, hx, hxne⟩ := hz.exists_hasEigenvector
  have heq : T x = z • x := mem_eigenspace_iff.mp hx
  have h := T.le_opNorm x
  rw [heq, norm_smul] at h
  exact le_of_mul_le_mul_right h (norm_pos_iff.mpr hxne)

private theorem eigenspaceTrace_support_subset (T A : H →L[ℂ] H) (hT : T.IsSymmetric)
    {R : ℝ} (hR : ‖T‖ ≤ R) :
    Function.support (fun z => eigenspaceTrace T z A) ⊆
      {z | starRingEnd ℂ z = z ∧ ‖z‖ ≤ R} := by
  intro z hz
  have he : HasEigenvalue T.toLinearMap z := by
    by_contra h
    exact hz (eigenspaceTrace_eq_zero_of_not_hasEigenvalue T z A h)
  exact ⟨hT.conj_eigenvalue_eq_self he, (hasEigenvalue_norm_le T he).trans hR⟩

private theorem trace_power_hasSum (T A : H →L[ℂ] H) (hT : IsTraceClass T)
    (hSymm : T.IsSymmetric) (k : ℕ) :
    HasSum (fun z : ℂ => eigenspaceTrace T z A * z ^ (k + 1))
      (operatorTrace (A * T ^ (k + 1))) := by
  have hCompact : IsCompactOperator T :=
    hilbertSchmidtCompact H H T (isHilbertSchmidt_of_isTraceClass T hT)
  let W := fun z : ℂ => eigenspace T.toLinearMap z
  have hW : IsHilbertSum ℂ (fun z => W z) (fun z => (W z).subtypeₗᵢ) :=
    IsHilbertSum.mkInternal W hSymm.orthogonalFamily_eigenspaces
      (Submodule.topologicalClosure_eq_top_iff.mpr
        (T.orthogonalComplement_iSup_eigenspaces_eq_bot hCompact hSymm)).ge
  have hClass : IsTraceClass (A * T ^ (k + 1)) := by
    rw [pow_succ, ← mul_assoc]
    exact isTraceClass_postcomp T (A * T ^ k) hT
  refine (hilbertSum_trace_hasSum W hW _ hClass).2.congr_fun (fun z => ?_)
  have hpow (x : W z) (j : ℕ) : (T ^ j) x = z ^ j • (x : H) := by
    have hx : T x = z • (x : H) := mem_eigenspace_iff.mp x.property
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ' T, mul_apply_eq_comp, ih, map_smul, hx, smul_smul, pow_succ]
  have hcompression :
      (W z).orthogonalProjectionOnto ∘L (A * T ^ (k + 1)) ∘L (W z).subtypeL =
        (z ^ (k + 1)) • ((W z).orthogonalProjectionOnto ∘L A ∘L (W z).subtypeL) := by
    ext1 x
    simp only [mul_apply_eq_comp, ContinuousLinearMap.comp_apply,
      Submodule.subtypeL_apply, smul_apply, hpow, map_smul]
  rw [hcompression]
  by_cases hz : z = 0
  · subst z
    have hzero : (0 : ℂ) • ((W 0).orthogonalProjectionOnto ∘L A ∘L (W 0).subtypeL) = 0 := by
      ext1 x
      exact zero_smul ℂ _
    rw [zero_pow (Nat.succ_ne_zero k), hzero, operatorTrace_zero, mul_zero]
  · let : FiniteDimensional ℂ (W z) := T.finite_dimensional_eigenspace hCompact z hz
    rw [operatorTrace_smul _ _ (isTraceClass_of_finiteDimensional _), mul_comm]
    rfl

end OneSpace

private theorem zero_of_moments {S : Set ℂ} (hS : IsCompact S)
    (hReal : ∀ z ∈ S, starRingEnd ℂ z = z) (c : S → ℂ)
    (hMoment : ∀ k : ℕ, HasSum (fun z : S => c z * (z : ℂ) ^ k) 0) (z : S) :
    c z = 0 := by
  let χ : S → Unit → (Polynomial ℂ →ₐ[ℂ] ℂ) := fun z _ => Polynomial.aeval (z : ℂ)
  have hsum : HasSum c 0 := by simpa using hMoment 0
  have hPoly (p : Polynomial ℂ) : HasSum (fun z : S => c z * p.eval (z : ℂ)) 0 := by
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simpa only [Polynomial.eval_add, mul_add, add_zero] using hp.add hq
    | monomial k a =>
      simpa only [Polynomial.eval_monomial, mul_left_comm (c _), mul_zero] using
        (hMoment k).mul_left a
  have hBound (_ : Unit) (p : Polynomial ℂ) : ∃ C : ℝ, ∀ z : S, ‖p.eval (z : ℂ)‖ ≤ C := by
    obtain ⟨C, hC⟩ := (hS.image p.continuous.norm).bddAbove
    exact ⟨C, fun z => hC ⟨z, z.property, rfl⟩⟩
  have hStar (x : Unit) (p : Polynomial ℂ) :
      ∃ q : Polynomial ℂ, ∀ z, χ z x q = starRingEnd ℂ (χ z x p) := by
    refine ⟨p.map (starRingEnd ℂ), fun z => ?_⟩
    change (p.map (starRingEnd ℂ)).eval (z : ℂ) = starRingEnd ℂ (p.eval (z : ℂ))
    simpa only [hReal z z.property] using
      Polynomial.eval_map_apply (starRingEnd ℂ) (p := p) (z : ℂ)
  have hProd (J : Finset Unit) (p : Unit → Polynomial ℂ) :
      HasSum (fun z => c z * ∏ x ∈ J, χ z x (p x)) 0 := by
    have hJ : J = ∅ ∨ J = {()} := by
      by_cases h : () ∈ J
      · right
        ext ⟨⟩
        simp [h]
      · left
        ext ⟨⟩
        simp [h]
    rcases hJ with rfl | rfl
    · simpa using hsum
    · simpa [χ] using hPoly (p ())
  have hfiber := boundedCharacterSeparation S Unit (fun _ => Polynomial ℂ) χ c
    hsum.summable (fun x p => hBound x p) hStar hProd z
  let z₀ : {y : S // ∀ x, χ y x = χ z x} := ⟨z, fun _ => rfl⟩
  have hpoint (y : {y : S // ∀ x, χ y x = χ z x}) : y = z₀ := by
    apply Subtype.ext
    apply Subtype.ext
    simpa [χ, z₀] using DFunLike.congr_fun (y.property ()) Polynomial.X
  rw [← hfiber.tsum_eq, tsum_eq_single z₀]
  exact fun y hy => (hy (hpoint y)).elim

/-- Comparing all positive-power traces for the elementary tests lets one replace
them on each nonzero finite-dimensional eigenspace and then sum the replacement traces. -/
def CompactOperatorTraceReplacementStatement : Prop :=
  ∀ (H₁ : Type u) (H₂ : Type v)
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] [CompleteSpace H₁]
    [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] [CompleteSpace H₂]
    (T₁ : H₁ →L[ℂ] H₁) (T₂ : H₂ →L[ℂ] H₂)
    (ι : Type w) (A₁ : ι → H₁ →L[ℂ] H₁) (A₂ : ι → H₂ →L[ℂ] H₂)
    (B₁ : H₁ →L[ℂ] H₁) (B₂ : H₂ →L[ℂ] H₂),
    IsTraceClass T₁ → IsTraceClass T₂ → T₁.IsSymmetric → T₂.IsSymmetric →
    (∀ i k, operatorTrace (A₁ i * T₁ ^ (k + 1)) = operatorTrace (A₂ i * T₂ ^ (k + 1))) →
    (∀ z : ℂ, z ≠ 0 →
      (∀ i, eigenspaceTrace T₁ z (A₁ i) = eigenspaceTrace T₂ z (A₂ i)) →
      eigenspaceTrace T₁ z B₁ = eigenspaceTrace T₂ z B₂) →
    operatorTrace (B₁ * T₁) = operatorTrace (B₂ * T₂)

theorem compactOperatorTraceReplacement : CompactOperatorTraceReplacementStatement.{u, v, w} := by
  intro H₁ H₂ _ _ _ _ _ _ T₁ T₂ ι A₁ A₂ B₁ B₂ hT₁ hT₂ hS₁ hS₂ hPowers hReplace
  let R := max ‖T₁‖ ‖T₂‖
  let S : Set ℂ := {z | starRingEnd ℂ z = z ∧ ‖z‖ ≤ R}
  have hS : IsCompact S := by
    apply (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset
    · exact (isClosed_eq continuous_star continuous_id).inter
        (isClosed_le continuous_norm continuous_const)
    · intro z hz
      exact Metric.mem_closedBall.mpr (by simpa using hz.2)
  have hSupport₁ (A : H₁ →L[ℂ] H₁) : Function.support (fun z => eigenspaceTrace T₁ z A) ⊆ S :=
    eigenspaceTrace_support_subset T₁ A hS₁ (le_max_left _ _)
  have hSupport₂ (A : H₂ →L[ℂ] H₂) : Function.support (fun z => eigenspaceTrace T₂ z A) ⊆ S :=
    eigenspaceTrace_support_subset T₂ A hS₂ (le_max_right _ _)
  have hEq (z : S) (hz : (z : ℂ) ≠ 0) (i : ι) :
      eigenspaceTrace T₁ z (A₁ i) = eigenspaceTrace T₂ z (A₂ i) := by
    let c : ℂ → ℂ := fun z => (eigenspaceTrace T₁ z (A₁ i) - eigenspaceTrace T₂ z (A₂ i)) * z
    have hMoment (k : ℕ) : HasSum (fun z : S => c z * (z : ℂ) ^ k) 0 := by
      have h := (trace_power_hasSum T₁ (A₁ i) hT₁ hS₁ k).sub
        (trace_power_hasSum T₂ (A₂ i) hT₂ hS₂ k)
      rw [hPowers i k, sub_self] at h
      apply (hasSum_subtype_iff_of_support_subset
        (f := fun x => c x * x ^ k) (s := S) ?_).2
      · simpa only [c, pow_succ', sub_mul, mul_assoc] using h
      · intro x hx
        contrapose! hx
        have h₁ : eigenspaceTrace T₁ x (A₁ i) = 0 := by
          by_contra hne
          exact hx (hSupport₁ (A₁ i) hne)
        have h₂ : eigenspaceTrace T₂ x (A₂ i) = 0 := by
          by_contra hne
          exact hx (hSupport₂ (A₂ i) hne)
        simp [c, h₁, h₂]
    have hzero := zero_of_moments hS (fun _ hz => hz.1) (fun z : S => c z) hMoment z
    exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_right hz)
  have h := (trace_power_hasSum T₁ B₁ hT₁ hS₁ 0).sub
    (trace_power_hasSum T₂ B₂ hT₂ hS₂ 0)
  have hTerms (z : ℂ) :
      eigenspaceTrace T₁ z B₁ * z ^ (0 + 1) - eigenspaceTrace T₂ z B₂ * z ^ (0 + 1) = 0 := by
    by_cases hz : z = 0
    · simp [hz]
    by_cases hzS : z ∈ S
    · rw [hReplace z hz (hEq ⟨z, hzS⟩ hz), sub_self]
    · have h₁ : eigenspaceTrace T₁ z B₁ = 0 := by
        by_contra hne
        exact hzS (hSupport₁ B₁ hne)
      have h₂ : eigenspaceTrace T₂ z B₂ = 0 := by
        by_contra hne
        exact hzS (hSupport₂ B₂ hne)
      simp [h₁, h₂]
  have hzero : HasSum (fun _ : ℂ => 0)
      (operatorTrace (B₁ * T₁ ^ (0 + 1)) - operatorTrace (B₂ * T₂ ^ (0 + 1))) :=
    h.congr_fun (fun z => (hTerms z).symm)
  simpa using sub_eq_zero.mp (hzero.unique hasSum_zero)

end Langlands.TraceFormula
