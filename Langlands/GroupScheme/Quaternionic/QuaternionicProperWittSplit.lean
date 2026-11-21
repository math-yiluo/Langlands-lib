import Langlands.GroupScheme.Quaternionic.QuaternionicSplitScalarGram
import Langlands.GroupScheme.Quaternionic.MatrixReducedNorm
import Langlands.LinearAlgebra.NumberFieldGramIsometry
import Langlands.LinearAlgebra.QuadraticReflectionGeneration
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Proper Witt transitivity in a split quaternion chart -/

noncomputable section

universe u v w

open Matrix
open scoped TensorProduct

namespace Langlands.GroupScheme.Quaternionic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

section ScalarExtension

variable {K : Type u} [Field K] [Invertible (2 : K)]
  {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {U : Type w} [AddCommGroup U] [Module K U] [FiniteDimensional K U]

private theorem exists_proper_isometryEquiv_match_embeddings
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate)
    (S : QuadraticForm K U) (hS : S.polarBilin.Nondegenerate)
    (f g : U →ₗ[K] V) (hf : ∀ x, Q (f x) = S x) (hg : ∀ x, Q (g x) = S x)
    (hdim : Module.finrank K U < Module.finrank K V) :
    ∃ e : Q.IsometryEquiv Q, e.toLinearEquiv.toLinearMap.det = 1 ∧ ∀ x, e (f x) = g x := by
  obtain ⟨e, he⟩ := Langlands.QuadraticForm.exists_isometryEquiv_match_embeddings Q S hS f g hf hg
  by_cases hdet : e.toLinearEquiv.toLinearMap.det = 1
  · exact ⟨e, hdet, he⟩
  have hd : e.toLinearEquiv.toLinearMap.det = -1 := by
    obtain ⟨l, hl⟩ := Langlands.QuadraticForm.exists_reflectionWord Q hQ e
    rw [← hl, Langlands.QuadraticForm.det_reflectionWord] at hdet ⊢
    rcases Nat.even_or_odd l.length with h | h
    · exact (hdet h.neg_one_pow).elim
    · exact h.neg_one_pow
  let B : LinearMap.BilinForm K V := Q.polarBilin
  have hB : B.IsSymm := ⟨fun x y => QuadraticMap.polar_comm Q x y⟩
  have hpolar (x y : U) : B (g x) (g y) = S.polarBilin x y := by
    simp only [B, QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, ← map_add g, hg]
  have hginj : Function.Injective g := by
    apply LinearMap.ker_eq_bot.mp
    rw [LinearMap.ker_eq_bot']
    intro x hx
    exact hS.1 x fun y => by rw [← hpolar, hx, map_zero, LinearMap.zero_apply]
  let W := LinearMap.range g
  let j : U ≃ₗ[K] W := LinearEquiv.ofInjective g hginj
  have hW : (B.restrict W).Nondegenerate := by
    have h : B.restrict W = LinearMap.BilinForm.congr j S.polarBilin := by
      ext a b
      obtain ⟨x, rfl⟩ := j.surjective a
      obtain ⟨y, rfl⟩ := j.surjective b
      rw [LinearMap.BilinForm.congr_apply, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
      exact hpolar x y
    rw [h]
    exact LinearMap.BilinForm.Nondegenerate.congr j hS
  let C := B.orthogonal W
  have hcompl : IsCompl W C := B.isCompl_orthogonal_of_restrict_nondegenerate hB.isRefl hW
  have hC : (B.restrict C).Nondegenerate := by
    apply (B.restrict_nondegenerate_iff_isCompl_orthogonal hB.isRefl).mpr
    change IsCompl C (B.orthogonal (B.orthogonal W))
    rw [B.orthogonal_orthogonal hQ hB.isRefl]
    exact hcompl.symm
  have hCdim : 0 < Module.finrank K C := by
    change 0 < Module.finrank K (B.orthogonal W)
    rw [B.finrank_orthogonal hQ, ← j.finrank_eq]
    omega
  let : Nontrivial C := Module.nontrivial_of_finrank_pos hCdim
  obtain ⟨z, hz⟩ : ∃ z : C, Q (z : V) ≠ 0 := by
    by_contra! h
    obtain ⟨r, hr⟩ := exists_ne (0 : C)
    apply hr (hC.1 r fun t => ?_)
    change Q.polarBilin (r : V) (t : V) = 0
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, ← Submodule.coe_add, h, h, h, sub_zero, sub_zero]
  let r := Langlands.QuadraticForm.reflection Q (z : V) hz
  refine ⟨e.trans r, ?_, fun x => ?_⟩
  · change (r.toLinearEquiv.toLinearMap.comp e.toLinearEquiv.toLinearMap).det = 1
    rw [LinearMap.det_comp, show r.toLinearEquiv.toLinearMap.det = -1 from
      Langlands.QuadraticForm.det_reflection Q (z : V) hz, hd, neg_mul_neg, one_mul]
  · change r (e (f x)) = g x
    rw [he, show r (g x) = g x - (QuadraticMap.polar Q (g x) z / Q z) • (z : V) from
      Langlands.QuadraticForm.reflection_apply Q _ _ _]
    have hzero : QuadraticMap.polar Q (g x) (z : V) = 0 := z.property _ ⟨x, rfl⟩
    rw [hzero, zero_div, zero_smul, sub_zero]

end ScalarExtension

section SplitMatrix

variable {R : Type u} {A : Type v} [Field R] [Ring A] [Algebra R A]
  {I : Type} [Fintype I] [DecidableEq I]
  (e : A ≃ₐ[R] Matrix (Fin 2) (Fin 2) R)

local notation "J" => FirstKindInvolution.gramTwo R
local notation "φ" => Matrix.compRingEquiv I (Fin 2) R

private def splitMatrixEquiv :
    Matrix I I A ≃+* Matrix (I × Fin 2) (I × Fin 2) R :=
  (e.mapMatrix (m := I)).toRingEquiv.trans φ

local notation "ψ" => splitMatrixEquiv (I := I) e

private theorem splitMatrixEquiv_apply (P : Matrix I I A) (i j : I) (a b : Fin 2) :
    ψ P (i, a) (j, b) = e (P i j) a b := rfl

private theorem splitSkewRows_vecMul (x : I → A) (P : Matrix I I A) :
    splitSkewRows e (x ᵥ* P) = splitSkewRows e x * ψ P := by
  ext a ⟨j, b⟩
  simp only [splitSkewRows, Matrix.of_apply, Matrix.vecMul, dotProduct, map_sum, map_mul,
    Matrix.sum_apply, Matrix.mul_apply, splitMatrixEquiv_apply, Fintype.sum_prod_type]

omit [Fintype I] [DecidableEq I] in
private theorem splitSkewRows_injective : Function.Injective (splitSkewRows (I := I) e) := by
  intro x y h
  funext i
  apply e.injective
  ext a b
  exact congrArg (fun M : Matrix (Fin 2) (I × Fin 2) R => M a (i, b)) h

omit [Fintype I] [DecidableEq I] in
private theorem splitSkewScalarGram_injective :
    Function.Injective (splitSkewScalarGram (I := I) e) := by
  intro H G heq
  let hJ : IsUnit (J : Matrix (Fin 2) (Fin 2) R) := FirstKindInvolution.isUnit_gramTwo
  ext i j
  apply e.injective
  have h : e (H i j) * J = e (G i j) * J := by
    ext a b
    have h' := congrArg (fun M : Matrix (I × Fin 2) (I × Fin 2) R => M (i, a) (j, b)) heq
    simpa only [splitSkewScalarGram_apply] using h'
  have h' := congrArg (· * (↑hJ.unit⁻¹ : Matrix (Fin 2) (Fin 2) R)) h
  simpa only [mul_assoc, hJ.mul_val_inv, mul_one] using h'

private theorem splitSkewScalarGram_eq_mul (H : Matrix I I A) :
    splitSkewScalarGram e H = ψ H * φ (Matrix.diagonal fun _ : I => J) := by
  change _ = φ (H.map e) * φ (Matrix.diagonal fun _ : I => J)
  rw [← map_mul]
  ext ⟨i, a⟩ ⟨j, b⟩
  rw [splitSkewScalarGram_apply, Matrix.compRingEquiv_apply, Matrix.comp_apply]
  rw [Matrix.mul_diagonal, Matrix.map_apply]

variable (τ : FirstKindInvolution R A)
  (hτ : ∀ a : A, e (τ a) * FirstKindInvolution.gramTwo R =
    FirstKindInvolution.gramTwo R * (e a)ᵀ)

include hτ in
private theorem splitMatrixEquiv_adjoint_mul (P : Matrix I I A) :
    ψ (τ.matrix I P) * φ (Matrix.diagonal fun _ : I => J) =
      φ (Matrix.diagonal fun _ : I => J) * (ψ P)ᵀ := by
  let L := Matrix.diagonal fun _ : I => J
  change φ ((τ.matrix I P).map e) * φ L = φ L * (φ (P.map e))ᵀ
  have h : (φ (P.map e))ᵀ = φ ((P.map e)ᵀ.map (·ᵀ)) := rfl
  rw [h, ← map_mul, ← map_mul]
  apply congrArg φ
  ext i j : 1
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply, Matrix.map_apply,
    Matrix.transpose_apply, Matrix.map_apply, FirstKindInvolution.matrix_apply]
  exact hτ (P j i)

include hτ in
private theorem splitSkewScalarGram_congruence (H P : Matrix I I A) :
    splitSkewScalarGram e (P * H * τ.matrix I P) =
      ψ P * splitSkewScalarGram e H * (ψ P)ᵀ := by
  rw [splitSkewScalarGram_eq_mul, splitSkewScalarGram_eq_mul, map_mul, map_mul,
    mul_assoc (ψ P * ψ H), splitMatrixEquiv_adjoint_mul e τ hτ]
  simp only [mul_assoc]

variable [CharZero R]

include hτ in
private theorem splitSkew_exists_properIsometry (hI : 2 ≤ Fintype.card I)
    (H : Matrix I I A) (hH : τ.matrix I H = -H) (hu : IsUnit H) (x y : I → A)
    (hx : IsUnit (τ.matrixSesqBilin H x x))
    (hxy : τ.matrixSesqBilin H x x = τ.matrixSesqBilin H y y) :
    ∃ p : (Matrix I I A)ˣ, (p : Matrix I I A) * H * τ.matrix I p = H ∧
      (ψ p).det = 1 ∧ x ᵥ* (p : Matrix I I A) = y := by
  let : Invertible (2 : R) := invertibleOfNonzero (two_ne_zero : (2 : R) ≠ 0)
  let C := splitSkewScalarGram e H
  let X := splitSkewRows e x
  let Y := splitSkewRows e y
  let S := e (τ.matrixSesqBilin H x x) * J
  have hsC : Cᵀ = C := splitSkewScalarGram_isSymm e τ hτ hH
  have huC : IsUnit C := splitSkewScalarGram_isUnit e hu
  have hxS : X * C * Xᵀ = S := (matrixSesqBilin_splitSkewScalarGram e τ hτ H x x).symm
  have hyS : Y * C * Yᵀ = S := by
    rw [← matrixSesqBilin_splitSkewScalarGram e τ hτ H y y, ← hxy]
  have hsS : Sᵀ = S := by
    rw [← hxS, Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hsC,
      Matrix.mul_assoc]
  have huS : IsUnit S := (hx.map e).mul FirstKindInvolution.isUnit_gramTwo
  let Q := C.toQuadraticForm'
  let T := S.toQuadraticForm'
  let f := X.vecMulLinear
  let g := Y.vecMulLinear
  have hMatrix (Z : Matrix (Fin 2) (I × Fin 2) R) :
      LinearMap.toMatrix' Z.vecMulLinear = Zᵀ := by
    rw [show Z.vecMulLinear = (Zᵀ).toLin' by
      rw [Matrix.toLin'_apply', Matrix.mulVecLin_transpose], LinearMap.toMatrix'_toLin']
  have hQ (Z : Matrix (Fin 2) (I × Fin 2) R) (h : Z * C * Zᵀ = S) : Q.comp Z.vecMulLinear = T := by
    apply Langlands.LinearAlgebra.OrthogonalCocycleDescent.quadratic_toMatrix_injective
    rw [QuadraticForm.toMatrix'_comp, hMatrix, Matrix.transpose_transpose,
      show Q.toMatrix' = C from Langlands.LinearAlgebra.OrthogonalCocycleDescent.toMatrix_toQuadraticForm_of_symm hsC,
      show T.toMatrix' = S from Langlands.LinearAlgebra.OrthogonalCocycleDescent.toMatrix_toQuadraticForm_of_symm hsS]
    exact h
  have hdim : Module.finrank R (Fin 2 → R) < Module.finrank R (I × Fin 2 → R) := by
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin]
    omega
  obtain ⟨a, hdet, ha⟩ := exists_proper_isometryEquiv_match_embeddings Q
    (Langlands.LinearAlgebra.OrthogonalCocycleDescent.polar_nondegenerate_of_symmetric_unit hsC huC) T
    (Langlands.LinearAlgebra.OrthogonalCocycleDescent.polar_nondegenerate_of_symmetric_unit hsS huS) f g
    (fun t => DFunLike.congr_fun (hQ X hxS) t) (fun t => DFunLike.congr_fun (hQ Y hyS) t) hdim
  let M := LinearMap.toMatrix' a.toLinearEquiv.toLinearMap
  let P := Mᵀ
  have hM : IsUnit M := LinearMap.isUnit_toMatrix'_iff.mpr
    ((Module.End.isUnit_iff _).mpr a.toLinearEquiv.bijective)
  have huP : IsUnit P := (Matrix.isUnit_transpose M).mpr hM
  let p := Units.map (ψ).symm.toMonoidHom huP.unit
  have hP : ψ (p : Matrix I I A) = P := by
    change ψ ((ψ).symm (↑huP.unit)) = P
    rw [RingEquiv.apply_symm_apply, huP.unit_spec]
  have hpres : P * C * Pᵀ = C := by
    have h : Q.comp a.toLinearEquiv.toLinearMap = Q := QuadraticMap.ext a.map_app
    have h' := congrArg QuadraticForm.toMatrix' h
    simpa only [QuadraticForm.toMatrix'_comp, P, M, Matrix.transpose_transpose,
      show Q.toMatrix' = C from Langlands.LinearAlgebra.OrthogonalCocycleDescent.toMatrix_toQuadraticForm_of_symm hsC]
      using h'
  have hsend : X * P = Y := by
    have h : a.toLinearEquiv.toLinearMap.comp X.vecMulLinear = Y.vecMulLinear := LinearMap.ext ha
    have ht := congrArg LinearMap.toMatrix' h
    rw [LinearMap.toMatrix'_comp, hMatrix, hMatrix] at ht
    simpa only [P, M, Matrix.transpose_mul, Matrix.transpose_transpose] using congrArg Matrix.transpose ht
  refine ⟨p, ?_, ?_, ?_⟩
  · apply splitSkewScalarGram_injective e
    rw [splitSkewScalarGram_congruence e τ hτ, hP]
    exact hpres
  · rw [hP, show P = Mᵀ from rfl, Matrix.det_transpose, LinearMap.det_toMatrix']
    exact hdet
  · apply splitSkewRows_injective e
    rw [splitSkewRows_vecMul, hP]
    exact hsend

end SplitMatrix

section Actual

open FiniteAlgebraUnits.MatrixPoints

variable {F D R : Type u} [Field F] [CharZero F] [DivisionRing D] [Algebra F D]
  [FiniteDimensional F D] [Algebra.IsCentral F D] [Field R] [Algebra F R]
  {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]

local notation "A" => R ⊗[F] D

omit [CharZero F] [FiniteDimensional F D] [Algebra.IsCentral F D] in
private theorem chartR_self (e : A ≃ₐ[R] Matrix (Fin 2) (Fin 2) R) (a : A) :
    DegreeSplitting.chartR e R a = e a := by
  refine TensorProduct.inductionOn (motive := fun t : A => DegreeSplitting.chartR e R t = e t) a ?_ ?_
  · intro r d
    rw [DegreeSplitting.chartR_tmul, Algebra.algebraMap_self]
    change r • e ((1 : R) ⊗ₜ[F] d) = e (r ⊗ₜ[F] d)
    rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  · intro a b ha hb
    rw [map_add, map_add, ha, hb]

omit [CharZero F] in
private theorem matrixReducedNorm_eq_det_splitMatrixEquiv
    (e : A ≃ₐ[R] Matrix (Fin 2) (Fin 2) R) (P : Matrix I I A) :
    matrixReducedNorm R P = (splitMatrixEquiv e P).det := by
  change Langlands.CentralSimple.reducedNorm F (Matrix I I D) R ((coefficientEquiv F D R).symm P) = _
  rw [DegreeSplitting.reducedNorm_eq_det_matrixChartR e]
  congr 1
  ext ⟨i, a⟩ ⟨j, b⟩
  rw [DegreeSplitting.matrixChartR_apply, AlgEquiv.apply_symm_apply,
    splitMatrixEquiv_apply, chartR_self e]

/-- Proper Witt transitivity for the actual scalar-extended skew matrix in
  a two-by-two splitting chart. -/
theorem quaternionic_exists_properIsometry_split
    (σ : FirstKindInvolution F D) (hdim : Module.finrank F D = 4)
    (hsym : Module.finrank F σ.symmetricSubspace = 3)
    (e : A ≃ₐ[R] Matrix (Fin 2) (Fin 2) R)
    (hI : 2 ≤ Fintype.card I) (H : Matrix I I A)
    (hH : ((σ.quaternionConjugation hdim hsym).baseChange R).matrix I H = -H) (hu : IsUnit H)
    (x y : I → A)
    (hx : IsUnit (((σ.quaternionConjugation hdim hsym).baseChange R).matrixSesqBilin H x x))
    (hxy : ((σ.quaternionConjugation hdim hsym).baseChange R).matrixSesqBilin H x x =
      ((σ.quaternionConjugation hdim hsym).baseChange R).matrixSesqBilin H y y) :
    ∃ p : (Matrix I I A)ˣ,
      (p : Matrix I I A) * H * ((σ.quaternionConjugation hdim hsym).baseChange R).matrix I p = H ∧
      matrixReducedNorm R (p : Matrix I I A) = 1 ∧ x ᵥ* (p : Matrix I I A) = y := by
  let : CharZero R := charZero_of_injective_algebraMap (algebraMap F R).injective
  obtain ⟨p, hp, hd, hsend⟩ := splitSkew_exists_properIsometry e
    ((σ.quaternionConjugation hdim hsym).baseChange R)
    (σ.splitQuaternionConjugation_mul_gramTwo hdim hsym e) hI H hH hu x y hx hxy
  have hn : matrixReducedNorm R (p : Matrix I I A) = 1 := by
    rw [matrixReducedNorm_eq_det_splitMatrixEquiv (F := F) (D := D) (I := I) e]
    exact hd
  exact ⟨p, hp, hn, hsend⟩

end Actual

/-- Over a splitting field, two rows of the same invertible skew value
  are related by an isometry of reduced norm one. -/
def QuaternionicProperWittSplitStatement : Prop :=
  ∀ (F D R : Type u) [Field F] [CharZero F] [DivisionRing D] [Algebra F D]
    [FiniteDimensional F D] [Algebra.IsCentral F D] [Field R] [Algebra F R]
    (σ : FirstKindInvolution F D) (hdim : Module.finrank F D = 4)
    (hsym : Module.finrank F σ.symmetricSubspace = 3),
    let A := R ⊗[F] D
    let τ := (σ.quaternionConjugation hdim hsym).baseChange R
    ∀ (_ : A ≃ₐ[R] Matrix (Fin 2) (Fin 2) R)
      (I : Type) [Fintype I] [DecidableEq I] [Nonempty I], 2 ≤ Fintype.card I →
    ∀ (H : Matrix I I A), τ.matrix I H = -H → IsUnit H →
    ∀ (x y : I → A), IsUnit (τ.matrixSesqBilin H x x) →
      τ.matrixSesqBilin H x x = τ.matrixSesqBilin H y y →
      ∃ p : (Matrix I I A)ˣ, (p : Matrix I I A) * H * τ.matrix I p = H ∧
        matrixReducedNorm R (p : Matrix I I A) = 1 ∧ x ᵥ* (p : Matrix I I A) = y

theorem quaternionicProperWittSplit : QuaternionicProperWittSplitStatement.{u} := by
  intro F D R _ _ _ _ _ _ _ _ σ hdim hsym A τ e I _ _ _ hI H hH hu x y hx hxy
  exact quaternionic_exists_properIsometry_split σ hdim hsym e hI H hH hu x y hx hxy

end Langlands.GroupScheme.Quaternionic
