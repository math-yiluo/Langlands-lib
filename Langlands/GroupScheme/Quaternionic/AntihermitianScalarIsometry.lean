import Langlands.Algebra.CentralSimple.MatrixSemilinearInvolution
import Langlands.GroupScheme.Quaternionic.AntihermitianForm
import Langlands.GroupScheme.Quaternionic.RationalIsometry
import Langlands.LinearAlgebra.QuadraticWittExtension
import Mathlib.Algebra.Module.Submodule.Equiv

/-! # Recovering antihermitian isometry from scalar quadratic isometry -/

noncomputable section

universe u v w t

namespace Langlands.GroupScheme.Quaternionic.AntihermitianForm

variable {F : Type u} {D : Type v} [Field F] [DivisionRing D] [Algebra F D]
  {σ : FirstKindInvolution F D}

section Pairings

variable {V : Type w} [AddCommGroup V] [Module D V] [Module F V] [IsScalarTower F D V]
  {W : Type t} [AddCommGroup W] [Module D W] [Module F W] [IsScalarTower F D W]
  (B : AntihermitianForm σ V) (C : AntihermitianForm σ W)

private theorem self_mem_alternating [Invertible (2 : F)] (x : V) :
    B x x ∈ σ.alternatingSubspace := by
  have hx : σ (B x x) = -B x x := by
    simpa only [neg_neg] using (congrArg Neg.neg (B.skew x x)).symm
  refine σ.mem_alternatingSubspace.mpr ⟨(⅟(2 : F)) • B x x, ?_⟩
  rw [σ.map_smul, hx, smul_neg, sub_neg_eq_add, invOf_two_smul_add_invOf_two_smul]

private theorem line_separating {x : V} (hx : B x x ≠ 0) :
    (B.pullback (lineMap x)).toBilin.SeparatingLeft := by
  intro a ha
  have h := ha 1
  change (B.pullback (lineMap x)) a 1 = 0 at h
  simp only [pullback_apply, lineMap_apply, one_smul, B.smul_left, mul_eq_zero] at h
  exact h.resolve_right hx

private def orthogonalLineScalarIsometry (ℓ : D →ₗ[F] F) (hℓ : ∃ a, ℓ (a - σ a) ≠ 0)
    {x : V} {y : W} (g : (B.scalarQuadratic ℓ).IsometryEquiv (C.scalarQuadratic ℓ))
    (hg : ∀ a : D, g (a • x) = a • y) :
    ((B.pullback (B.orthogonalLine x).subtype).scalarQuadratic ℓ).IsometryEquiv
      ((C.pullback (C.orthogonalLine y).subtype).scalarQuadratic ℓ) := by
  let P := (B.orthogonalLine x).restrictScalars F
  let Q := (C.orthogonalLine y).restrictScalars F
  have hmem (z : V) : z ∈ P ↔ g z ∈ Q := by
    change z ∈ B.orthogonalLine x ↔ g z ∈ C.orthogonalLine y
    rw [B.mem_orthogonalLine_iff_scalar ℓ hℓ, C.mem_orthogonalLine_iff_scalar ℓ hℓ]
    apply forall_congr'
    intro a
    rw [← hg a]
    simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, ← map_add g, g.map_app]
  have hmap : P.map g.toLinearEquiv.toLinearMap = Q := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact (hmem w).mp hw
    · intro hz
      obtain ⟨w, rfl⟩ := g.toLinearEquiv.surjective z
      exact ⟨w, (hmem w).mpr hz, rfl⟩
  exact { g.toLinearEquiv.ofSubmodules P Q hmap with map_app' := fun z => g.map_app z }

end Pairings

variable [Invertible (2 : F)] [FiniteDimensional F D]

private theorem exists_equiv_of_scalarQuadratic_aux
    (ℓ : D →ₗ[F] F) (hℓ : ∃ a, ℓ (a - σ a) ≠ 0)
    (hcoord : ∀ a ∈ σ.alternatingSubspace, ℓ a = 0 → a = 0) (n : ℕ) :
    ∀ {V : Type w} [AddCommGroup V] [Module D V] [Module F V] [IsScalarTower F D V]
      [FiniteDimensional D V]
      {W : Type t} [AddCommGroup W] [Module D W] [Module F W] [IsScalarTower F D W]
      [FiniteDimensional D W]
      (B : AntihermitianForm σ V) (C : AntihermitianForm σ W),
      B.toBilin.SeparatingLeft → C.toBilin.SeparatingLeft →
      Module.finrank D V = n → Module.finrank D W = n →
      (B.scalarQuadratic ℓ).IsometryEquiv (C.scalarQuadratic ℓ) →
      ∃ e : V ≃ₗ[D] W, ∀ z z', C (e z) (e z') = B z z' := by
  induction n with
  | zero =>
    intro V _ _ _ _ _ W _ _ _ _ _ B C _ _ hV hW _
    let : Subsingleton V := Module.finrank_zero_iff.mp hV
    let : Subsingleton W := Module.finrank_zero_iff.mp hW
    refine ⟨LinearEquiv.ofSubsingleton V W, fun z z' => ?_⟩
    rw [Subsingleton.elim z 0, Subsingleton.elim z' 0, map_zero, B.zero_left, C.zero_left]
  | succ n ih =>
    intro V _ _ _ _ _ W _ _ _ _ _ B C hB hC hV hW f
    let : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hV
    obtain ⟨x, hx⟩ : ∃ x, B.scalarQuadratic ℓ x ≠ 0 := by
      by_contra! h
      obtain ⟨z, hz⟩ := exists_ne (0 : V)
      apply hz ((B.scalarQuadratic_nondegenerate hB ℓ hℓ).1 z ?_)
      intro w
      change (B.scalarQuadratic ℓ).polarBilin z w = 0
      simp only [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar, h, sub_zero]
    let y := f x
    have hxy : B x x = C y y := by
      apply sub_eq_zero.mp
      apply hcoord _ (σ.alternatingSubspace.sub_mem (B.self_mem_alternating x)
        (C.self_mem_alternating y))
      rw [map_sub]
      exact sub_eq_zero.mpr (f.map_app x).symm
    have hx' : B x x ≠ 0 := by
      intro h
      exact hx (by simp [h])
    have hy' : C y y ≠ 0 := hxy ▸ hx'
    let S := (B.pullback (lineMap x)).scalarQuadratic ℓ
    have hS := (B.pullback (lineMap x)).scalarQuadratic_nondegenerate (B.line_separating hx') ℓ hℓ
    let i : D →ₗ[F] W := f.toLinearEquiv.toLinearMap.comp ((lineMap (D := D) x).restrictScalars F)
    let j : D →ₗ[F] W := (lineMap (D := D) y).restrictScalars F
    have hi (a : D) : C.scalarQuadratic ℓ (i a) = S a := f.map_app _
    have hj (a : D) : C.scalarQuadratic ℓ (j a) = S a := by
      change ℓ (C (a • y) (a • y)) = ℓ (B (a • x) (a • x))
      simp only [smul_left, smul_right, hxy]
    obtain ⟨e, he⟩ := Langlands.QuadraticForm.exists_isometryEquiv_match_embeddings
      (C.scalarQuadratic ℓ) S hS i j hi hj
    let g := f.trans e
    have hg (a : D) : g (a • x) = a • y := he a
    have hrB := (B.splitLine x hx').finrank_eq
    have hrC := (C.splitLine y hy').finrank_eq
    simp only [Module.finrank_prod, Module.finrank_self] at hrB hrC
    obtain ⟨d, hd⟩ := ih (B.pullback (B.orthogonalLine x).subtype)
      (C.pullback (C.orthogonalLine y).subtype)
      (B.orthogonalLine_separatingLeft hB x hx') (C.orthogonalLine_separatingLeft hC y hy')
      (by omega) (by omega) (B.orthogonalLineScalarIsometry C ℓ hℓ g hg)
    let E := (B.splitLine x hx').symm.trans
      (((LinearEquiv.refl D D).prodCongr d).trans (C.splitLine y hy'))
    refine ⟨E, fun v w => ?_⟩
    obtain ⟨p, rfl⟩ := (B.splitLine x hx').surjective v
    obtain ⟨q, rfl⟩ := (B.splitLine x hx').surjective w
    have hpq : C (d p.2) (d q.2) = B p.2 q.2 := hd p.2 q.2
    simp only [E, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply, LinearEquiv.prodCongr_apply,
      LinearEquiv.refl_apply, splitLine_pairing, hpq, hxy]

/-- A separating antihermitian pairing is recovered up to division-linear isometry
from its scalar quadratic form when the scalar coordinate detects alternating values. -/
theorem exists_equiv_of_scalarQuadratic
    {V : Type w} [AddCommGroup V] [Module D V] [Module F V] [IsScalarTower F D V]
    [FiniteDimensional D V]
    {W : Type t} [AddCommGroup W] [Module D W] [Module F W] [IsScalarTower F D W]
    [FiniteDimensional D W]
    (B : AntihermitianForm σ V) (C : AntihermitianForm σ W)
    (hB : B.toBilin.SeparatingLeft) (hC : C.toBilin.SeparatingLeft)
    (hr : Module.finrank D V = Module.finrank D W)
    (ℓ : D →ₗ[F] F) (hℓ : ∃ a, ℓ (a - σ a) ≠ 0)
    (hcoord : ∀ a ∈ σ.alternatingSubspace, ℓ a = 0 → a = 0)
    (f : (B.scalarQuadratic ℓ).IsometryEquiv (C.scalarQuadratic ℓ)) :
    ∃ e : V ≃ₗ[D] W, ∀ z z', C (e z) (e z') = B z z' :=
  exists_equiv_of_scalarQuadratic_aux ℓ hℓ hcoord (Module.finrank D V) B C hB hC rfl hr.symm f

end Langlands.GroupScheme.Quaternionic.AntihermitianForm

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution

open Matrix

private theorem exists_vecMul_eq_linearMap {D : Type v} [DivisionRing D]
    {ι : Type w} [Fintype ι] [DecidableEq ι] (f : (ι → D) →ₗ[D] (ι → D)) :
    ∃ P : Matrix ι ι D, ∀ x, x ᵥ* P = f x := by
  let P : Matrix ι ι D := Matrix.of fun i => f (Pi.single i 1)
  have h : Langlands.Algebra.CentralSimple.rowMulLinear P = f := by
    apply (Pi.basisFun D ι).ext
    intro i
    rw [Pi.basisFun_apply, Langlands.Algebra.CentralSimple.rowMulLinear_apply,
      Matrix.single_one_vecMul]
    rfl
  exact ⟨P, DFunLike.congr_fun h⟩

/-- For invertible antihermitian matrices over a division algebra, isometry
of the scalar quadratic forms implies Gram congruence. -/
def MatrixScalarIsometryReflectionStatement : Prop :=
  ∀ (F : Type u) (D : Type v) [Field F] [DivisionRing D] [Algebra F D]
    [Invertible (2 : F)] [FiniteDimensional F D]
    (σ : FirstKindInvolution F D) (ι : Type w) [Fintype ι] [DecidableEq ι]
    (ℓ : D →ₗ[F] F) (H H' : Matrix ι ι D),
    (∃ a, ℓ (a - σ a) ≠ 0) →
    (∀ a ∈ σ.alternatingSubspace, ℓ a = 0 → a = 0) →
    σ.IsAntihermitian H → σ.IsAntihermitian H' → IsUnit H → IsUnit H' →
    (σ.scalarQuadratic ℓ H').Equivalent (σ.scalarQuadratic ℓ H) →
    ∃ P : (Matrix ι ι D)ˣ, (P : Matrix ι ι D) * H * σ.matrix ι P = H'

theorem matrixScalarIsometryReflection : MatrixScalarIsometryReflectionStatement.{u, v, w} := by
  intro F D _ _ _ _ _ σ ι _ _ ℓ H H' hℓ hcoord hH hH' hu hu' ⟨f⟩
  obtain ⟨e, he⟩ := AntihermitianForm.exists_equiv_of_scalarQuadratic
    (AntihermitianForm.ofMatrix hH') (AntihermitianForm.ofMatrix hH)
    (AntihermitianForm.ofMatrix_separatingLeft hH' hu')
    (AntihermitianForm.ofMatrix_separatingLeft hH hu) rfl ℓ hℓ hcoord f
  obtain ⟨P, hP⟩ := exists_vecMul_eq_linearMap e.toLinearMap
  obtain ⟨Q, hQ⟩ := exists_vecMul_eq_linearMap e.symm.toLinearMap
  have hPQ : P * Q = 1 := Matrix.ext_iff_vecMul.mpr fun x => by
    rw [← Matrix.vecMul_vecMul, hQ, hP, Matrix.vecMul_one]
    exact e.symm_apply_apply x
  have hQP : Q * P = 1 := Matrix.ext_iff_vecMul.mpr fun x => by
    rw [← Matrix.vecMul_vecMul, hP, hQ, Matrix.vecMul_one]
    exact e.apply_symm_apply x
  refine ⟨⟨P, Q, hPQ, hQP⟩, ?_⟩
  change P * H * σ.matrix ι P = H'
  apply Eichler.matrix_eq_of_sesqForm_eq σ
  intro x y
  rw [← σ.sesqForm_vecMul, hP, hP]
  exact he x y

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution
