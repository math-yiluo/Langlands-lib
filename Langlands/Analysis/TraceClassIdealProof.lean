import Langlands.Analysis.TraceClassIdealStatement
import Langlands.Analysis.TraceClassFactorizationProof
import Langlands.Analysis.HilbertSchmidtProductTraceClassProof
import Mathlib.Analysis.InnerProductSpace.ProdL2

noncomputable section

namespace Langlands.Analysis.OperatorIdeals

universe u v

variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem isTraceClass_zero : IsTraceClass (0 : E →L[ℂ] E) := by
  simpa only [ContinuousLinearMap.zero_comp] using
    hilbertSchmidtProductTraceClass E E (0 : E →L[ℂ] E) 0
      isHilbertSchmidt_zero isHilbertSchmidt_zero

theorem isTraceClass_add (A D : E →L[ℂ] E)
    (hA : IsTraceClass A) (hD : IsTraceClass D) : IsTraceClass (A + D) := by
  obtain ⟨U₁, V₁, hU₁, hV₁, h₁⟩ := traceClassFactorization E A hA
  obtain ⟨U₂, V₂, hU₂, hV₂, h₂⟩ := traceClassFactorization E D hD
  let H := WithLp 2 (E × E)
  let I : E →L[ℂ] H :=
    (WithLp.prodContinuousLinearEquiv 2 ℂ E E).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.inl ℂ E E)
  let J : E →L[ℂ] H :=
    (WithLp.prodContinuousLinearEquiv 2 ℂ E E).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.inr ℂ E E)
  let R : E →L[ℂ] H := I.comp V₁ + J.comp V₂
  let Q : H →L[ℂ] E :=
    U₁.comp (WithLp.fstL 2 ℂ E E) + U₂.comp (WithLp.sndL 2 ℂ E E)
  have hR : IsHilbertSchmidt R :=
    isHilbertSchmidt_add _ _
      (isHilbertSchmidt_postcomp V₁ I hV₁)
      (isHilbertSchmidt_postcomp V₂ J hV₂)
  have hQ : IsHilbertSchmidt Q :=
    isHilbertSchmidt_add _ _
      (isHilbertSchmidt_precomp U₁ (WithLp.fstL 2 ℂ E E) hU₁)
      (isHilbertSchmidt_precomp U₂ (WithLp.sndL 2 ℂ E E) hU₂)
  have hprod : Q.comp R = A + D := by
    rw [h₁, h₂]
    ext x
    change U₁ (V₁ x + 0) + U₂ (0 + V₂ x) = U₁ (V₁ x) + U₂ (V₂ x)
    simp
  rw [← hprod]
  exact hilbertSchmidtProductTraceClass E H R Q hR hQ

theorem isTraceClass_smul (c : ℂ) (A : E →L[ℂ] E) (hA : IsTraceClass A) :
    IsTraceClass (c • A) := by
  obtain ⟨U, V, hU, hV, hfac⟩ := traceClassFactorization E A hA
  rw [hfac, ← ContinuousLinearMap.smul_comp]
  exact hilbertSchmidtProductTraceClass E E V (c • U) hV
    (isHilbertSchmidt_smul c U hU)

theorem isTraceClass_adjoint (A : E →L[ℂ] E) (hA : IsTraceClass A) :
    IsTraceClass A.adjoint := by
  obtain ⟨U, V, hU, hV, hfac⟩ := traceClassFactorization E A hA
  rw [hfac, ContinuousLinearMap.adjoint_comp]
  exact hilbertSchmidtProductTraceClass E E U.adjoint V.adjoint
    (isHilbertSchmidt_adjoint U hU) (isHilbertSchmidt_adjoint V hV)

theorem isTraceClass_adjoint_iff (A : E →L[ℂ] E) :
    IsTraceClass A ↔ IsTraceClass A.adjoint := by
  refine ⟨isTraceClass_adjoint A, fun h => ?_⟩
  simpa only [ContinuousLinearMap.adjoint_adjoint] using
    isTraceClass_adjoint A.adjoint h

theorem isTraceClass_sandwich (A : E →L[ℂ] E)
    (B : E →L[ℂ] F) (C : F →L[ℂ] E) (hA : IsTraceClass A) :
    IsTraceClass ((B.comp A).comp C) := by
  obtain ⟨U, V, hU, hV, hfac⟩ := traceClassFactorization E A hA
  have h := hilbertSchmidtProductTraceClass F E (V.comp C) (B.comp U)
    (isHilbertSchmidt_precomp V C hV) (isHilbertSchmidt_postcomp U B hU)
  simpa only [hfac, ContinuousLinearMap.comp_assoc] using h

theorem isTraceClass_postcomp (A B : E →L[ℂ] E) (hA : IsTraceClass A) :
    IsTraceClass (B.comp A) := by
  simpa only [ContinuousLinearMap.comp_id] using
    isTraceClass_sandwich A B (ContinuousLinearMap.id ℂ E) hA

theorem isTraceClass_precomp (A C : E →L[ℂ] E) (hA : IsTraceClass A) :
    IsTraceClass (A.comp C) := by
  simpa only [ContinuousLinearMap.id_comp] using
    isTraceClass_sandwich A (ContinuousLinearMap.id ℂ E) C hA

theorem traceClassIdeal : TraceClassIdealStatement.{u, v} := by
  intro E F _ _ _ _ _ _
  exact ⟨isTraceClass_zero, isTraceClass_add, isTraceClass_smul,
    isTraceClass_adjoint_iff, isTraceClass_sandwich⟩

end Langlands.Analysis.OperatorIdeals
