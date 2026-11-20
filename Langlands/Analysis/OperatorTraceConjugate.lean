import Langlands.Analysis.OperatorTraceProof
import Langlands.Analysis.HilbertSchmidtProductTraceClassProof

/-! # Conjugation by a conjugate-linear Hilbert isometry -/

noncomputable section

open scoped ComplexConjugate InnerProductSpace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Analysis.OperatorIdeals

variable {H J : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup J] [InnerProductSpace ℂ J]
  (e : H ≃ₗᵢ⋆[ℂ] J)

/-- Conjugation by a conjugate-linear isometric equivalence sends a bounded
complex-linear operator to another bounded complex-linear operator. -/
def conjugateHilbertOperator (T : H →L[ℂ] H) : J →L[ℂ] J where
  toFun y := e (T (e.symm y))
  map_add' x y := by simp only [map_add]
  map_smul' c x := by
    simp only [map_smulₛₗ, Complex.conj_conj, RingHom.id_apply]
  cont := e.continuous.comp (T.continuous.comp e.symm.continuous)

@[simp]
theorem conjugateHilbertOperator_apply (T : H →L[ℂ] H) (x : H) :
    conjugateHilbertOperator e T (e x) = e (T x) := by
  change e (T (e.symm (e x))) = _
  rw [LinearIsometryEquiv.symm_apply_apply]

theorem conjugateHilbertOperator_comp (T U : H →L[ℂ] H) :
    conjugateHilbertOperator e (T.comp U) =
      (conjugateHilbertOperator e T).comp (conjugateHilbertOperator e U) := by
  apply ContinuousLinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := e.surjective y
  simp only [conjugateHilbertOperator_apply, ContinuousLinearMap.comp_apply]

variable [CompleteSpace J]
  (he : ∀ (x y : H), ⟪e x, e y⟫_ℂ = conj ⟪x, y⟫_ℂ)

omit [CompleteSpace J] in
include he in
private theorem orthonormal_conjugate_basis {ι : Type*} (b : HilbertBasis ι ℂ H) :
    Orthonormal ℂ (fun i => e (b i)) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  rw [he, orthonormal_iff_ite.mp b.orthonormal]
  split_ifs <;> simp

omit [CompleteSpace J] in
include he in
private theorem orthogonal_conjugate_basis_eq_bot {ι : Type*} (b : HilbertBasis ι ℂ H) :
    (Submodule.span ℂ (Set.range fun i => e (b i)))ᗮ = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨y, rfl⟩ := e.surjective x
  have hy (i : ι) : ⟪b i, y⟫_ℂ = 0 := by
    have hb : e (b i) ∈ Submodule.span ℂ (Set.range fun j => e (b j)) :=
      Submodule.subset_span ⟨i, rfl⟩
    have h := Submodule.inner_right_of_mem_orthogonal hb hx
    rw [he] at h
    simpa only [Complex.conj_conj, map_zero] using congrArg (starRingEnd ℂ) h
  have hzero : y = 0 := by
    apply b.repr.injective
    rw [map_zero]
    ext i
    rw [b.repr_apply_apply]
    exact hy i
  rw [hzero, map_zero, Submodule.mem_bot]

/-- The Hilbert basis obtained by applying a conjugate-linear Hilbert isometry
to the vectors of a Hilbert basis. -/
def conjugateHilbertBasis {ι : Type*} (b : HilbertBasis ι ℂ H) : HilbertBasis ι ℂ J :=
  HilbertBasis.mkOfOrthogonalEqBot (orthonormal_conjugate_basis e he b)
    (orthogonal_conjugate_basis_eq_bot e he b)

@[simp]
theorem conjugateHilbertBasis_apply {ι : Type*} (b : HilbertBasis ι ℂ H) (i : ι) :
    conjugateHilbertBasis e he b i = e (b i) :=
  congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot _ _) i

include he in
/-- Conjugation preserves the Hilbert–Schmidt condition. -/
theorem isHilbertSchmidt_conjugateHilbertOperator (T : H →L[ℂ] H) (hT : IsHilbertSchmidt T) :
    IsHilbertSchmidt (conjugateHilbertOperator e T) := by
  obtain ⟨s, b, hb⟩ := hT
  let c := conjugateHilbertBasis e he b
  have hc : Summable (fun i => ‖conjugateHilbertOperator e T (c i)‖ ^ 2) := by
    simpa only [c, conjugateHilbertBasis_apply, conjugateHilbertOperator_apply,
      LinearIsometryEquiv.norm_map] using hb
  obtain ⟨t, d, _⟩ := exists_hilbertBasis ℂ J
  exact ⟨t, d, (hilbertSchmidtBasisIndependence J J s t _ c d).1.mp hc⟩

variable [CompleteSpace H]

include he in
/-- Conjugation preserves the trace-class condition, by Hilbert–Schmidt factorization. -/
theorem isTraceClass_conjugateHilbertOperator (T : H →L[ℂ] H) (hT : IsTraceClass T) :
    IsTraceClass (conjugateHilbertOperator e T) := by
  obtain ⟨U, V, hU, hV, hUV⟩ := traceClassFactorization H T hT
  rw [hUV, conjugateHilbertOperator_comp]
  exact hilbertSchmidtProductTraceClass J J _ _
    (isHilbertSchmidt_conjugateHilbertOperator e he V hV)
    (isHilbertSchmidt_conjugateHilbertOperator e he U hU)

include he in
/-- The trace of a trace-class operator is conjugated by a conjugate-linear Hilbert isometry. -/
theorem operatorTrace_conjugateHilbertOperator (T : H →L[ℂ] H) (hT : IsTraceClass T) :
    operatorTrace (conjugateHilbertOperator e T) = conj (operatorTrace T) := by
  obtain ⟨s, b, _⟩ := exists_hilbertBasis ℂ H
  let c := conjugateHilbertBasis e he b
  rw [(operatorTraceBasis J _ s c (isTraceClass_conjugateHilbertOperator e he T hT)).2,
    (operatorTraceBasis H T s b hT).2, traceIn, traceIn, Complex.conj_tsum]
  exact tsum_congr fun i => by
    simp only [c, conjugateHilbertBasis_apply, conjugateHilbertOperator_apply, he]

end Langlands.Analysis.OperatorIdeals
