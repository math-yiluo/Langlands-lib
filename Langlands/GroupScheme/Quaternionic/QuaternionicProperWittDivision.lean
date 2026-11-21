import Langlands.GroupScheme.Quaternionic.RankOneReducedNorm
import Langlands.GroupScheme.Quaternionic.QuaternionConjugation
import Langlands.GroupScheme.Quaternionic.HyperbolicLevi

/-! # Proper Witt transitivity over quaternion division coefficients -/

noncomputable section

universe u

open Matrix
open scoped TensorProduct

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution.Eichler

open Langlands.CentralSimple FiniteAlgebraUnits.MatrixPoints

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1900000

section Norm

variable {F D : Type u} [Field F] [DivisionRing D] [Algebra F D]
  [Algebra.IsCentral F D] [FiniteDimensional F D] (σ : FirstKindInvolution F D)
  {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]

local notation "N" => reducedNorm F D F

private theorem reducedNorm_tmul_involution (a : D) :
    N ((1 : F) ⊗ₜ[F] σ a) = N ((1 : F) ⊗ₜ[F] a) := by
  let d : Fin 1 → F ⊗[F] D := fun _ => (1 : F) ⊗ₜ[F] a
  let e : Fin 1 → F ⊗[F] D := fun _ => (1 : F) ⊗ₜ[F] σ a
  have hdiag : (σ.baseChange F).matrix (Fin 1) (Matrix.diagonal d) = Matrix.diagonal e := by
    ext i j
    obtain rfl := Subsingleton.elim i j
    rw [FirstKindInvolution.matrix_apply, Matrix.diagonal_apply_eq, Matrix.diagonal_apply_eq,
      show d i = (1 : F) ⊗ₜ[F] a from rfl, FirstKindInvolution.baseChange_tmul]
  have h := matrixReducedNorm_adjoint F σ (Matrix.diagonal d)
  rw [hdiag, matrixReducedNorm_diagonal, matrixReducedNorm_diagonal, Fin.prod_univ_one, Fin.prod_univ_one] at h
  exact h

private theorem reducedNorm_neg_one (hdim : Module.finrank F D = 4) :
    N ((1 : F) ⊗ₜ[F] (-1 : D)) = 1 := by
  rw [TensorProduct.tmul_neg, ← TensorProduct.neg_tmul,
    reducedNorm_scalar, reducedDegree_eq_two_of_finrank_four hdim]
  norm_num

private theorem reducedNorm_tmul_neg (hdim : Module.finrank F D = 4) (a : D) :
    N ((1 : F) ⊗ₜ[F] (-a)) = N ((1 : F) ⊗ₜ[F] a) := by
  calc
    N ((1 : F) ⊗ₜ[F] (-a)) = N (((1 : F) ⊗ₜ[F] (-1 : D)) * ((1 : F) ⊗ₜ[F] a)) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, neg_one_mul]
    _ = _ := by rw [_root_.map_mul, reducedNorm_neg_one hdim, one_mul]

omit σ in
private theorem reducedNorm_matrix_tmul_neg_one (hdim : Module.finrank F D = 4) :
    reducedNorm F (Matrix I I D) F ((1 : F) ⊗ₜ[F] (-1 : Matrix I I D)) = 1 := by
  let d : I → F ⊗[F] D := fun _ => (1 : F) ⊗ₜ[F] (-1 : D)
  have hd : coefficientEquiv F D F ((1 : F) ⊗ₜ[F] (-1 : Matrix I I D)) = Matrix.diagonal d := by
    ext i j
    rw [coefficientEquiv_tmul, Matrix.neg_apply]
    by_cases h : i = j
    · subst j
      rw [Matrix.one_apply_eq, Matrix.diagonal_apply_eq]
    · rw [Matrix.one_apply_ne h, Matrix.diagonal_apply_ne _ h, neg_zero, TensorProduct.tmul_zero]
  have h := matrixReducedNorm_diagonal (K := F) (D := D) F d
  rw [← hd, show (∏ i : I, N (d i)) = 1 by simp [d, reducedNorm_neg_one hdim]] at h
  change reducedNorm F (Matrix I I D) F ((coefficientEquiv F D F).symm
    (coefficientEquiv F D F ((1 : F) ⊗ₜ[F] (-1 : Matrix I I D)))) = 1 at h
  simpa only [AlgEquiv.symm_apply_apply] using h

/-- An admissible quaternionic reflection has reduced norm one. -/
theorem reflectionMatrix_reducedNorm_one (hdim : Module.finrank F D = 4)
    (q : σ.QuadraticForms I) {y : I → D} {c : D} (hc : c ≠ 0)
    (hcq : (Submodule.Quotient.mk c : D ⧸ σ.alternatingSubspace) = σ.quadraticValue y q) :
    reducedNorm F (Matrix I I D) F ((1 : F) ⊗ₜ[F] reflectionMatrix σ q y c) = 1 := by
  have hyy := sesqForm_polar_self_of_quadraticValue σ q hcq
  rw [reflectionMatrix, formRankOne, reducedNorm_matrix_one_sub_vecMulVec]
  have hcontract : (c⁻¹ • y) ⬝ᵥ (σ.polar q *ᵥ (σ ∘ y)) = c⁻¹ * (c + σ c) := by
    rw [← σ.sesqForm_eq_dotProduct, σ.sesqForm_smul_left, hyy]
  rw [hcontract, mul_add, inv_mul_cancel₀ hc, sub_add_cancel_left]
  rw [reducedNorm_tmul_neg hdim]
  have hn : N ((1 : F) ⊗ₜ[F] (c⁻¹ * σ c)) = N (((1 : F) ⊗ₜ[F] c⁻¹) * ((1 : F) ⊗ₜ[F] σ c)) := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rw [hn, _root_.map_mul, reducedNorm_tmul_involution σ, ← _root_.map_mul,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, inv_mul_cancel₀ hc]
  exact _root_.map_one N

end Norm

section Isometry

variable {F D : Type u} [Field F] [CharZero F] [DivisionRing D] [Algebra F D]
  [Algebra.IsCentral F D] [FiniteDimensional F D] (σ : FirstKindInvolution F D)
  {I : Type} [Fintype I] [DecidableEq I] [Nonempty I] [LinearOrder I]
  (q : σ.QuadraticForms I)

local notation "B" => σ.sesqForm (σ.polar q)
local notation "Q" => fun v => σ.quadraticValue v q

omit [CharZero F] in
private theorem exists_properReflection_send (hdim : Module.finrank F D = 4)
    {x y : I → D} (hval : Q x = Q y) (hc : B x (x - y) ≠ 0) :
    ∃ g ∈ rationalIsometryGroup σ q,
      reducedNorm F (Matrix I I D) F ((1 : F) ⊗ₜ[F] (g : Matrix I I D)) = 1 ∧
      x ᵥ* (g : Matrix I I D) = y := by
  let c := B x (x - y)
  have hcq : (Submodule.Quotient.mk c : D ⧸ σ.alternatingSubspace) = Q (x - y) := by
    change Submodule.Quotient.mk (B x (x - y)) = σ.quadraticValue (x - y) q
    rw [sub_eq_add_neg, σ.sesqForm_add_right, Submodule.Quotient.mk_add,
      quotient_mk_sesqForm_polar_self, σ.quadraticValue_add, quadraticValue_neg]
    exact congrArg (fun v => σ.quadraticValue x q + v +
      Submodule.Quotient.mk (B x (-y))) hval
  obtain ⟨g, hg, hgval⟩ := exists_mem_reflectionSet σ q hc hcq
  refine ⟨g, reflectionSet_subset σ q hg, ?_, ?_⟩
  · rw [hgval]
    exact reflectionMatrix_reducedNorm_one σ hdim q hc hcq
  · rw [hgval, vecMul_reflectionMatrix, show B x (x - y) = c from rfl,
      mul_inv_cancel₀ hc, one_smul, sub_sub_cancel]

/-- Equal nonzero values lie in the same proper rational isometry orbit over a
  quaternion division algebra. -/
theorem exists_properIsometry_send (hdim : Module.finrank F D = 4)
    {x y : I → D} (hx : Q x ≠ 0) (hval : Q x = Q y) :
    ∃ g ∈ rationalIsometryGroup σ q,
      reducedNorm F (Matrix I I D) F ((1 : F) ⊗ₜ[F] (g : Matrix I I D)) = 1 ∧
      x ᵥ* (g : Matrix I I D) = y := by
  by_cases hc : B x (x - y) = 0
  · have hxx : B x x ≠ 0 := by
      intro h0
      have h := quotient_mk_sesqForm_polar_self σ q x
      rw [h0, Submodule.Quotient.mk_zero, ← two_smul F] at h
      exact hx ((smul_eq_zero.mp h.symm).resolve_left two_ne_zero)
    have hxy : B x y = B x x := by
      rw [sesqForm_sub_right, sub_eq_zero] at hc
      exact hc.symm
    have hc' : B x (x - -y) ≠ 0 := by
      rw [sub_neg_eq_add, σ.sesqForm_add_right, hxy, ← two_smul F]
      exact smul_ne_zero (two_ne_zero : (2 : F) ≠ 0) hxx
    have hval' : Q x = Q (-y) := hval.trans (quadraticValue_neg σ q y).symm
    obtain ⟨g, hmem, hnorm, hsend⟩ := exists_properReflection_send σ q hdim hval' hc'
    let m : (Matrix I I D)ˣ := -1
    have hm : m ∈ rationalIsometryGroup σ q := by
      rw [mem_rationalIsometryGroup_iff_forall]
      simp only [m, Units.val_neg, Units.val_one, Matrix.vecMul_neg, Matrix.vecMul_one,
        sesqForm_neg_left, sesqForm_neg_right, neg_neg, quadraticValue_neg]
      exact ⟨fun _ _ => True.intro, fun _ => True.intro⟩
    refine ⟨g * m, (rationalIsometryGroup σ q).mul_mem hmem hm, ?_, ?_⟩
    · rw [Units.val_mul, ← show ((1 : F) ⊗ₜ[F] (g : Matrix I I D)) * ((1 : F) ⊗ₜ[F] (m : Matrix I I D)) =
          (1 : F) ⊗ₜ[F] ((g : Matrix I I D) * (m : Matrix I I D)) by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul], _root_.map_mul, hnorm, one_mul]
      exact reducedNorm_matrix_tmul_neg_one hdim
    · rw [Units.val_mul, ← Matrix.vecMul_vecMul, hsend, show (m : Matrix I I D) = -1 from rfl,
        Matrix.vecMul_neg, Matrix.vecMul_one, neg_neg]
  · exact exists_properReflection_send σ q hdim hval hc

end Isometry

/-- Proper Witt transitivity in the actual quotient-valued quadratic form. -/
def QuaternionicProperWittDivisionStatement : Prop :=
  ∀ (F D : Type u) [Field F] [CharZero F] [DivisionRing D] [Algebra F D]
    [Algebra.IsCentral F D] [FiniteDimensional F D], Module.finrank F D = 4 →
    ∀ (σ : FirstKindInvolution F D) (I : Type) [Fintype I] [DecidableEq I] [Nonempty I] [LinearOrder I]
      (q : σ.QuadraticForms I) (x y : I → D),
    σ.quadraticValue x q ≠ 0 → σ.quadraticValue x q = σ.quadraticValue y q →
    ∃ g ∈ rationalIsometryGroup σ q,
      reducedNorm F (Matrix I I D) F ((1 : F) ⊗ₜ[F] (g : Matrix I I D)) = 1 ∧
      x ᵥ* (g : Matrix I I D) = y

theorem quaternionicProperWittDivision : QuaternionicProperWittDivisionStatement.{u} := by
  intro F D _ _ _ _ _ _ hdim σ I _ _ _ _ q x y hx hxy
  exact exists_properIsometry_send σ q hdim hx hxy

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution.Eichler
