import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.SymplecticGroup

/-! # Darboux normal form of alternating matrices over a field

A nondegenerate alternating bilinear form on a finite-dimensional vector space has a symplectic
family `v : Fin k ⊕ Fin k → V` whose Gram matrix (`gramMatrix`) is the standard alternating matrix
`J = [[0, -1], [1, 0]]` and with `2 k = dim V` (`exists_symplecticFamily`). In matrix terms: an
invertible matrix `C` over a field with `Cᵀ = -C` and zero diagonal satisfies `P C Pᵀ = J` for a
rectangular matrix `P` with a two-sided inverse (`exists_mul_mul_transpose_eq_J`).
-/

noncomputable section

open Matrix Module LinearMap.BilinForm
open LinearMap (BilinForm)

namespace Langlands.GroupScheme.SymplecticMatrix

universe w

variable {L : Type*} [Field L]

/-- An alternating form which is left separating is nondegenerate. -/
theorem nondegenerate_of_isAlt {V : Type*} [AddCommGroup V] [Module L V] {B : BilinForm L V}
    (hA : B.IsAlt) (h : LinearMap.SeparatingLeft B) : B.Nondegenerate :=
  ⟨h, fun y hy => h y fun x => by rw [← hA.neg_eq x y, hy x, neg_zero]⟩

/-- A nondegenerate alternating form on a space of dimension `N` has a family of `2 k = N`
vectors whose Gram matrix is `J`. -/
theorem exists_symplecticFamily_aux (N : ℕ) :
    ∀ (V : Type w) [AddCommGroup V] [Module L V] [FiniteDimensional L V], finrank L V = N →
      ∀ B : BilinForm L V, B.IsAlt → B.Nondegenerate →
        ∃ k : ℕ, 2 * k = N ∧ ∃ v : Fin k ⊕ Fin k → V, ∀ a b, B (v a) (v b) = J (Fin k) L a b := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro V _ _ _ hV B hA hN
  rcases Nat.eq_zero_or_pos N with hN0 | hN0
  · exact ⟨0, by omega, fun a => isEmptyElim a, fun a => isEmptyElim a⟩
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := L) (by omega)
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  obtain ⟨y, hy⟩ : ∃ y, B x y ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hx (hN.1 x hcon)
  set f : V := (-(B x y)⁻¹) • y with hf
  have hxf : B x f = -1 := by
    rw [hf, map_smul, smul_eq_mul, neg_mul, inv_mul_cancel₀ hy]
  have hfx : B f x = 1 := by rw [← hA.neg_eq, hxf, neg_neg]
  have hxx : B x x = 0 := hA.self_eq_zero x
  have hff : B f f = 0 := hA.self_eq_zero f
  have hpair : ∀ a c : L, B (a • x + c • f) x = c ∧ B (a • x + c • f) f = -a := by
    intro a c
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hxx,
      hfx, hxf, hff]
    constructor <;> ring
  have hli : LinearIndependent L ![x, f] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h := hpair s t
    rw [hst, map_zero, LinearMap.zero_apply, LinearMap.zero_apply] at h
    exact ⟨neg_eq_zero.1 h.2.symm, h.1.symm⟩
  set W : Submodule L V := Submodule.span L (Set.range ![x, f]) with hWdef
  have hxW : x ∈ W := Submodule.subset_span ⟨0, rfl⟩
  have hfW : f ∈ W := Submodule.subset_span ⟨1, rfl⟩
  have hWrank : finrank L W = 2 := by
    rw [hWdef, finrank_span_eq_card hli, Fintype.card_fin]
  have hW : (B.restrict W).Nondegenerate := by
    refine nondegenerate_of_isAlt (fun w => hA.self_eq_zero (w : V)) ?_
    rintro ⟨w, hw⟩ h0
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun L).1 hw
    have h1 : B (c 0 • x + c 1 • f) x = 0 := by
      have := h0 ⟨x, hxW⟩
      simpa [Fin.sum_univ_two] using this
    have h2 : B (c 0 • x + c 1 • f) f = 0 := by
      have := h0 ⟨f, hfW⟩
      simpa [Fin.sum_univ_two] using this
    rw [(hpair _ _).1] at h1
    rw [(hpair _ _).2, neg_eq_zero] at h2
    apply Subtype.ext
    simp [Fin.sum_univ_two, h1, h2]
  have hRefl := hA.isRefl
  have hcompl := isCompl_orthogonal_of_restrict_nondegenerate hRefl hW
  set W' : Submodule L V := B.orthogonal W with hW'def
  have hW' : (B.restrict W').Nondegenerate := by
    rw [restrict_nondegenerate_iff_isCompl_orthogonal hRefl, hW'def,
      orthogonal_orthogonal hN hRefl]
    exact hcompl.symm
  have hN2 : 2 ≤ N := by
    have := Submodule.finrank_le W
    omega
  have hW'rank : finrank L W' = N - 2 := by
    have := Submodule.finrank_add_eq_of_isCompl hcompl
    omega
  obtain ⟨k, hk, v, hv⟩ := ih (N - 2) (by omega) W' hW'rank (B.restrict W')
    (fun w => hA.self_eq_zero (w : V)) hW'
  have hv' : ∀ a b, B (v a : V) (v b : V) = J (Fin k) L a b := hv
  have hort : ∀ a, B x (v a : V) = 0 ∧ B f (v a : V) = 0 := fun a =>
    ⟨(v a).2 x hxW, (v a).2 f hfW⟩
  have hort' : ∀ a, B (v a : V) x = 0 ∧ B (v a : V) f = 0 := fun a =>
    ⟨hRefl _ _ (hort a).1, hRefl _ _ (hort a).2⟩
  refine ⟨k + 1, by omega, Sum.elim (fun i => Fin.cases x (fun j => (v (Sum.inl j) : V)) i)
    (fun i => Fin.cases f (fun j => (v (Sum.inr j) : V)) i), ?_⟩
  have h0s : ∀ i : Fin k, (0 : Fin (k + 1)) ≠ i.succ := fun i => (Fin.succ_ne_zero i).symm
  rintro (i | i) (j | j) <;> cases i using Fin.cases <;> cases j using Fin.cases <;>
    simp [J, hxx, hxf, hfx, hff, hort, hort', hv', Matrix.one_apply, h0s]

/-- The Gram matrix `(B (v a) (v b))_{a b}` of a family of vectors. -/
def gramMatrix {V : Type*} [AddCommGroup V] [Module L V] {ι : Type*} (B : BilinForm L V)
    (v : ι → V) : Matrix ι ι L :=
  Matrix.of fun a b => B (v a) (v b)

@[simp] theorem gramMatrix_apply {V : Type*} [AddCommGroup V] [Module L V] {ι : Type*}
    (B : BilinForm L V) (v : ι → V) (a b : ι) : gramMatrix B v a b = B (v a) (v b) :=
  rfl

/-- A nondegenerate alternating form has a family of `2 k = dim V` vectors whose Gram matrix
is `J`. -/
theorem exists_symplecticFamily {V : Type w} [AddCommGroup V] [Module L V] [FiniteDimensional L V]
    (B : BilinForm L V) (hA : B.IsAlt) (hN : B.Nondegenerate) :
    ∃ k : ℕ, 2 * k = finrank L V ∧ ∃ v : Fin k ⊕ Fin k → V, gramMatrix B v = J (Fin k) L := by
  obtain ⟨k, hk, v, hv⟩ := exists_symplecticFamily_aux _ V rfl B hA hN
  exact ⟨k, hk, v, Matrix.ext hv⟩

/-- The quadratic form of a matrix with `Cᵀ = -C` and zero diagonal vanishes. -/
theorem dotProduct_mulVec_self_eq_zero {m : Type*} [Fintype m] {C : Matrix m m L}
    (hC : Cᵀ = -C) (hd : ∀ i, C i i = 0) (x : m → L) : x ⬝ᵥ C *ᵥ x = 0 := by
  have h : x ⬝ᵥ C *ᵥ x = ∑ p : m × m, x p.1 * C p.1 p.2 * x p.2 := by
    simp only [dotProduct, mulVec, Finset.mul_sum, Fintype.sum_prod_type, mul_assoc]
  rw [h]
  refine Finset.sum_involution (fun p _ => p.swap) ?_ ?_ (fun _ _ => Finset.mem_univ _)
    (fun p _ => p.swap_swap)
  · rintro ⟨i, j⟩ _
    have hji : C j i = -C i j := by simpa using congrFun (congrFun hC i) j
    simp only [Prod.swap_prod_mk, hji]
    ring
  · rintro ⟨i, j⟩ _ hne heq
    simp only [Prod.swap_prod_mk, Prod.mk.injEq] at heq
    obtain ⟨rfl, -⟩ := heq
    exact hne (by simp [hd])

/-- **Darboux.** An invertible matrix over a field with `Cᵀ = -C` and zero diagonal is congruent
to `J`: there is a rectangular matrix `P` with two-sided inverse `P'` and `P C Pᵀ = J`. -/
theorem exists_mul_mul_transpose_eq_J {m : Type*} [Fintype m] [DecidableEq m]
    (C : Matrix m m L) (hC : Cᵀ = -C) (hd : ∀ i, C i i = 0) (hdet : C.det ≠ 0) :
    ∃ (k : ℕ) (P : Matrix (Fin k ⊕ Fin k) m L) (P' : Matrix m (Fin k ⊕ Fin k) L),
      P * P' = 1 ∧ P' * P = 1 ∧ P * C * Pᵀ = J (Fin k) L := by
  have hA : (Matrix.toBilin' C).IsAlt := fun x => by
    rw [Matrix.toBilin'_apply']
    exact dotProduct_mulVec_self_eq_zero hC hd x
  have hN : (Matrix.toBilin' C).Nondegenerate := nondegenerate_toBilin'_iff_det_ne_zero.2 hdet
  obtain ⟨k, hk, v, hv'⟩ := exists_symplecticFamily (Matrix.toBilin' C) hA hN
  have hv : ∀ a b, Matrix.toBilin' C (v a) (v b) = J (Fin k) L a b := fun a b => by
    rw [← hv', gramMatrix_apply]
  rw [Module.finrank_fintype_fun_eq_card] at hk
  let P : Matrix (Fin k ⊕ Fin k) m L := Matrix.of fun a i => v a i
  have hP : P * C * Pᵀ = J (Fin k) L := by
    ext a b
    rw [← hv a b, Matrix.toBilin'_apply']
    simp only [P, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, dotProduct, mulVec,
      Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  let e : (Fin k ⊕ Fin k) ≃ m := Fintype.equivOfCardEq (by simp; omega)
  let P₁ : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) L := P.submatrix id e
  have hP₁ : P₁ * C.submatrix e e * P₁ᵀ = J (Fin k) L := by
    simp only [P₁, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv]
    exact (congrArg (fun M => M.submatrix id id) hP).trans (Matrix.submatrix_id_id _)
  have hdetP₁ : P₁.det ≠ 0 := by
    intro h0
    have := congrArg Matrix.det hP₁
    rw [Matrix.det_mul, Matrix.det_mul, h0, zero_mul, zero_mul] at this
    exact (isUnit_det_J (Fin k) L).ne_zero this.symm
  have hunit : IsUnit P₁ := (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdetP₁)
  have hPeq : P = P₁.submatrix id e.symm := by
    ext a i
    simp [P₁]
  refine ⟨k, P, P₁⁻¹.submatrix e.symm id, ?_, ?_, hP⟩
  · rw [hPeq, Matrix.submatrix_mul_equiv, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hunit),
      Matrix.submatrix_id_id]
  · rw [hPeq, ← Matrix.submatrix_mul _ _ _ _ _ Function.bijective_id,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hunit),
      Matrix.submatrix_one_equiv]

/-- Let `P` be a rectangular matrix with a left inverse `P'` and `P C Pᵀ = J`. Then `P g P'` is
symplectic exactly when `g` preserves `C`, over any commutative ring. -/
theorem mul_mul_mem_symplecticGroup_iff {R : Type*} [CommRing R] {m : Type*} [Fintype m]
    [DecidableEq m] {k : ℕ} {P : Matrix (Fin k ⊕ Fin k) m R} {P' : Matrix m (Fin k ⊕ Fin k) R}
    {C : Matrix m m R} (h₂ : P' * P = 1) (hC : P * C * Pᵀ = J (Fin k) R)
    (g : Matrix m m R) :
    P * g * P' ∈ symplecticGroup (Fin k) R ↔ g * C * gᵀ = C := by
  have hT : Pᵀ * P'ᵀ = 1 := by rw [← transpose_mul, h₂, transpose_one]
  have key : P * g * P' * J (Fin k) R * (P * g * P')ᵀ = P * (g * C * gᵀ) * Pᵀ := by
    rw [← hC]
    simp only [transpose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc P' P, h₂, Matrix.one_mul, ← Matrix.mul_assoc Pᵀ P'ᵀ, hT,
      Matrix.one_mul]
  have hinj : ∀ X Y : Matrix m m R, P * X * Pᵀ = P * Y * Pᵀ → X = Y := by
    intro X Y h
    have h' := congrArg (fun Z => P' * Z * P'ᵀ) h
    have hT' : Pᵀ * P'ᵀ = 1 := hT
    simp only [Matrix.mul_assoc] at h'
    simpa only [← Matrix.mul_assoc P' P, h₂, hT', Matrix.one_mul, Matrix.mul_one] using h'
  rw [SymplecticGroup.mem_iff, key]
  constructor
  · intro h
    exact hinj _ _ (h.trans hC.symm)
  · intro h
    rw [h, hC]

end Langlands.GroupScheme.SymplecticMatrix
