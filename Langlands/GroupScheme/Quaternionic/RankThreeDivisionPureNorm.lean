import Langlands.GroupScheme.Quaternionic.SkewHermitianHyperbolicPair
import Langlands.GroupScheme.Quaternionic.HyperbolicBasis
import Langlands.GroupScheme.Quaternionic.KneserThreeQuaternion
import Langlands.GroupScheme.Quaternionic.MatrixReducedNorm

/-! # Pure quaternion norms of isotropic rank-three division forms -/

noncomputable section

universe u

open Matrix
open scoped TensorProduct

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution

open Langlands.CentralSimple

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000

variable {F D R : Type u} [Field F] [CharZero F] [DivisionRing D] [Algebra F D]
  [Algebra.IsCentral F D] [FiniteDimensional F D] [Field R] [Algebra F R]
  (σ : FirstKindInvolution F D) (hdim : Module.finrank F D = 4)
  (hsym : Module.finrank F σ.symmetricSubspace = 3)

local notation "A" => R ⊗[F] D
local notation "τ" => FirstKindInvolution.baseChange (σ.quaternionConjugation hdim hsym) R

omit [Algebra.IsCentral F D] in
private theorem baseChange_ne_id : ∃ a : A, τ a ≠ a := by
  let l := σ.quaternionAlternatingUnit hdim hsym
  refine ⟨(1 : R) ⊗ₜ[F] (l : D), ?_⟩
  rw [FirstKindInvolution.baseChange_tmul, KneserThree.Quaternion.conj_ell]
  intro hh
  have hinj : Function.Injective (fun a : D => (1 : R) ⊗ₜ[F] a) :=
    Algebra.TensorProduct.includeRight_injective (algebraMap F R).injective
  have h := congrArg (fun z : D => z + l) (hinj hh)
  rw [neg_add_cancel, ← two_smul F] at h
  exact (smul_ne_zero (two_ne_zero : (2 : F) ≠ 0) l.ne_zero) h.symm

include σ hdim hsym in
private theorem reducedNorm_neg (x : A) : reducedNorm F D R (-x) = reducedNorm F D R x := by
  apply (algebraMap R A).injective
  rw [← σ.quaternionConjugation_norm_baseChange hdim hsym R (-x),
    ← σ.quaternionConjugation_norm_baseChange hdim hsym R x,
    FirstKindInvolution.map_neg, neg_mul_neg]

private theorem rankThree_diagonal_congruence {K E : Type u} [Field K] [DivisionRing E]
    [Algebra K E] [Invertible (2 : K)]
    {ν : FirstKindInvolution K E} (hν : ∃ a, ν a ≠ a) {H : Matrix (Fin 3) (Fin 3) E}
    (hH : ν.IsAntihermitian H) (hu : IsUnit H) {x : Fin 3 → E}
    (hx : x ≠ 0) (hxx : ν.sesqForm H x x = 0) :
    ∃ (P : Matrix (Fin 3) (Fin 3) E) (a b : E),
      IsUnit P ∧ b ∈ ν.alternatingSubspace ∧ P * H * ν.matrix (Fin 3) P = Matrix.diagonal ![a, -a, b] := by
  let B := AntihermitianForm.ofMatrix hH
  have hB := AntihermitianForm.ofMatrix_separatingLeft hH hu
  obtain ⟨c, hc, ha, h₁⟩ := B.exists_rankThree_basis_of_isotropic hν hB (Module.finrank_fin_fun E) hx hxx
  let a := B (c 0) (c 0)
  let b := B (c 2) (c 2)
  have hb : b ≠ 0 := by
    intro hzero
    apply c.ne_zero 2
    apply hB
    intro y
    rw [← c.sum_repr y]
    change B.toBilin (c 2) (∑ i, c.repr y i • c i) = 0
    rw [_root_.map_sum]
    apply Finset.sum_eq_zero
    intro i _
    change B (c 2) (c.repr y i • c i) = 0
    rw [B.smul_right]
    by_cases hi : i = 2
    · subst i
      rw [show B (c 2) (c 2) = 0 from hzero, zero_mul]
    · rw [hc 2 i (Ne.symm hi), zero_mul]
  let P : Matrix (Fin 3) (Fin 3) E := Matrix.of c
  have hP : P * H * ν.matrix (Fin 3) P = Matrix.diagonal ![a, -a, b] := by
    ext i j
    rw [ν.mul_mul_matrix_apply, Matrix.diagonal_apply]
    change B (c i) (c j) = _
    by_cases hij : i = j
    · subst j
      rw [ite_eq_left rfl]
      fin_cases i
      · rfl
      · exact h₁
      · rfl
    · rw [ite_eq_right hij, hc i j hij]
  have hvec : IsUnit (![a, -a, b] : Fin 3 → E) := Pi.isUnit_iff.mpr fun i => by
    apply isUnit_iff_ne_zero.mpr
    fin_cases i
    · exact ha
    · exact neg_ne_zero.mpr ha
    · exact hb
  have hd := hvec.map (Matrix.diagonalRingHom (Fin 3) E)
  have hPu := ν.isUnit_of_mul_mul_matrix_eq hd hP
  exact ⟨P, a, b, hPu, ν.sesqForm_self_mem_alternatingSubspace hH (c 2), hP⟩

/-- At a field where the quaternion algebra is division, an isotropic invertible
  rank-three skew Gram matrix has reduced norm represented by a pure quaternion. -/
theorem exists_pureNorm_eq_matrixReducedNorm_of_isotropic [Invertible (2 : R)]
    (hdom : IsDomain A) (H : Matrix (Fin 3) (Fin 3) A) (hu : IsUnit H)
    (hH : (τ).matrix (Fin 3) H = -H) {x : Fin 3 → A}
    (hx : x ≠ 0) (hxx : ∑ i, ∑ j, x i * H i j * τ (x j) = 0) :
    ∃ y : A, y ∈ (τ).alternatingSubspace ∧ reducedNorm F D R y = matrixReducedNorm R H := by
  let : IsDomain A := hdom
  let : DivisionRing A := divisionRingOfFiniteDimensional R A
  have hanti : (τ).IsAntihermitian H := by
    refine ⟨hH, fun i => KneserThree.mem_alternatingSubspace_of_neg τ (h := ⅟ (2 : R)) (mul_invOf_self _) ?_⟩
    exact congrArg (fun P : Matrix (Fin 3) (Fin 3) A => P i i) hH
  obtain ⟨P, a, b, hP, hb, hdiag⟩ := rankThree_diagonal_congruence
    (σ.baseChange_ne_id hdim hsym) hanti hu hx hxx
  have hN : matrixReducedNorm R H * (matrixReducedNorm R P) ^ 2 =
      (reducedNorm F D R a) ^ 2 * reducedNorm F D R b := by
    rw [← matrixReducedNorm_congruence R (σ.quaternionConjugation hdim hsym), hdiag,
      matrixReducedNorm_diagonal, Fin.prod_univ_three]
    change reducedNorm F D R a * reducedNorm F D R (-a) * reducedNorm F D R b = _
    rw [σ.reducedNorm_neg hdim hsym, pow_two]
  have hdeg : reducedDegree F D = 2 := by
    rw [reducedDegree, hdim]
    exact Nat.sqrt_eq 2
  let c := reducedNorm F D R a / matrixReducedNorm R P
  refine ⟨c • b, (τ).alternatingSubspace.smul_mem c hb, ?_⟩
  have hscalar : reducedNorm F D R (algebraMap R A c) = c ^ 2 := by
    change reducedNorm F D R (c ⊗ₜ[F] (1 : D)) = c ^ 2
    rw [reducedNorm_scalar, hdeg]
  have hP0 : matrixReducedNorm R P ≠ 0 := (hP.map (matrixReducedNorm R)).ne_zero
  rw [Algebra.smul_def, _root_.map_mul, hscalar, show c = reducedNorm F D R a / matrixReducedNorm R P from rfl,
    div_pow, div_mul_eq_mul_div]
  exact (div_eq_iff (pow_ne_zero _ hP0)).mpr hN.symm

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution
