import Langlands.GroupScheme.OrthogonalMatrix.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Hyperbolic bases of quadratic forms over algebraically closed fields

Over an algebraically closed field `L` of any characteristic, a quadratic form `Q` on a space
of dimension `2 k` whose polar form is nondegenerate has a hyperbolic basis: vectors
`v : Fin k ⊕ Fin k → V` with `Q (v a) = 0` and polar Gram matrix `[[0, 1], [1, 0]]`
(`exists_hyperbolicFamily`). In matrix terms (`exists_hyperbolic_matrix`): for a matrix
`Q : Matrix n n L` with `Q + Qᵀ` invertible and `card n = 2 m` there is a rectangular matrix `P`
with a two-sided inverse such that `P Q Pᵀ - formMatrix (Fin m) L` is alternating, i.e. `P`
carries the quadratic form `x ↦ x Q xᵀ` to the split form `∑ a, x (inl a) * x (inr a)`.
-/

noncomputable section

open Matrix Module LinearMap.BilinForm
open LinearMap (BilinForm)
open scoped Matrix

namespace Langlands.GroupScheme.OrthogonalMatrix

universe w

variable {L : Type*} [Field L]

section Isotropic

variable {V : Type*} [AddCommGroup V] [Module L V]

/-- Expansion of a quadratic form along a line: `Q (x + t y) = Q x + t B(x, y) + t² Q y`. -/
theorem quadratic_add_smul (Q : QuadraticForm L V) (x y : V) (t : L) :
    Q (x + t • y) = Q x + t * QuadraticMap.polar Q x y + t * t * Q y := by
  have h : Q (x + t • y) = QuadraticMap.polar Q x (t • y) + Q x + Q (t • y) := by
    rw [QuadraticMap.polar]
    ring
  rw [h, QuadraticMap.polar_smul_right, QuadraticMap.map_smul, smul_eq_mul, smul_eq_mul]
  ring

/-- Over an algebraically closed field, every quadratic form on a space of dimension at least
two has a nonzero isotropic vector. -/
theorem exists_isotropic [IsAlgClosed L] [FiniteDimensional L V] (h : 1 < finrank L V)
    (Q : QuadraticForm L V) : ∃ e : V, e ≠ 0 ∧ Q e = 0 := by
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := L) (by omega)
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  obtain ⟨y, hxy⟩ := exists_linearIndependent_pair_of_one_lt_finrank h hx
  rw [LinearIndependent.pair_iff] at hxy
  by_cases hy : Q y = 0
  · refine ⟨y, fun h0 => ?_, hy⟩
    have := hxy 0 1 (by simp [h0])
    exact one_ne_zero this.2
  · obtain ⟨t, ht⟩ := IsAlgClosed.exists_root
      (Polynomial.C (Q y) * Polynomial.X ^ 2 + Polynomial.C (QuadraticMap.polar Q x y) *
        Polynomial.X + Polynomial.C (Q x))
      (by rw [Polynomial.degree_quadratic hy]; exact two_ne_zero)
    refine ⟨x + t • y, fun h0 => ?_, ?_⟩
    · have := hxy 1 t (by simpa using h0)
      exact one_ne_zero this.1
    · rw [quadratic_add_smul]
      simp only [Polynomial.IsRoot.def, Polynomial.eval_add, Polynomial.eval_mul,
        Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X] at ht
      linear_combination ht

/-- Over an algebraically closed field, a quadratic form of dimension at least two with left
separating polar form has a hyperbolic pair: `Q e = Q f = 0` and `B(e, f) = 1`. -/
theorem exists_hyperbolicPair [IsAlgClosed L] [FiniteDimensional L V] (h : 1 < finrank L V)
    (Q : QuadraticForm L V) (hQ : (QuadraticMap.polarBilin Q).SeparatingLeft) :
    ∃ e f : V, Q e = 0 ∧ Q f = 0 ∧ QuadraticMap.polar Q e f = 1 := by
  obtain ⟨e, he, hQe⟩ := exists_isotropic h Q
  obtain ⟨z, hz⟩ : ∃ z, QuadraticMap.polar Q e z ≠ 0 :=
    not_forall.mp fun hcon => he (hQ e fun y => hcon y)
  set f' : V := (QuadraticMap.polar Q e z)⁻¹ • z with hf'def
  have hf' : QuadraticMap.polar Q e f' = 1 := by
    rw [hf'def, QuadraticMap.polar_smul_right, smul_eq_mul, inv_mul_cancel₀ hz]
  refine ⟨e, f' + (-Q f') • e, hQe, ?_, ?_⟩
  · rw [quadratic_add_smul, QuadraticMap.polar_comm, hf', hQe]
    ring
  · rw [QuadraticMap.polar_add_right, hf', QuadraticMap.polar_smul_right,
      QuadraticMap.polar_self, hQe, smul_zero, smul_zero, add_zero]

end Isotropic

/-- **Hyperbolic basis.** Over an algebraically closed field, a quadratic form with
nondegenerate polar form on a space of dimension `2 k` has a family `v : Fin k ⊕ Fin k → V` of
isotropic vectors whose polar Gram matrix is `polarMatrix (Fin k) L = [[0, 1], [1, 0]]`. -/
theorem exists_hyperbolicFamily_aux [IsAlgClosed L] (k : ℕ) :
    ∀ (V : Type w) [AddCommGroup V] [Module L V] [FiniteDimensional L V], finrank L V = 2 * k →
      ∀ Q : QuadraticForm L V, (QuadraticMap.polarBilin Q).Nondegenerate →
        ∃ v : Fin k ⊕ Fin k → V, (∀ a, Q (v a) = 0) ∧
          ∀ a b, QuadraticMap.polar Q (v a) (v b) = polarMatrix (Fin k) L a b := by
  induction k with
  | zero =>
    intro V _ _ _ _ Q _
    exact ⟨fun a => isEmptyElim a, fun a => isEmptyElim a, fun a => isEmptyElim a⟩
  | succ k ih =>
  intro V _ _ _ hV Q hN
  set B : BilinForm L V := QuadraticMap.polarBilin Q with hBdef
  have hB : ∀ x y, B x y = QuadraticMap.polar Q x y := fun _ _ => rfl
  obtain ⟨x, f, hx, hf, hxf⟩ := exists_hyperbolicPair (by omega) Q hN.1
  have hfx : QuadraticMap.polar Q f x = 1 := by rw [QuadraticMap.polar_comm, hxf]
  have hxx : QuadraticMap.polar Q x x = 0 := by rw [QuadraticMap.polar_self, hx, smul_zero]
  have hff : QuadraticMap.polar Q f f = 0 := by rw [QuadraticMap.polar_self, hf, smul_zero]
  have hpair : ∀ a c : L, B (a • x + c • f) x = c ∧ B (a • x + c • f) f = a := by
    intro a c
    simp only [hB, QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left, smul_eq_mul, hxx,
      hfx, hxf, hff]
    constructor <;> ring
  have hli : LinearIndependent L ![x, f] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h := hpair s t
    rw [hst, map_zero, LinearMap.zero_apply, LinearMap.zero_apply] at h
    exact ⟨h.2.symm, h.1.symm⟩
  set W : Submodule L V := Submodule.span L (Set.range ![x, f]) with hWdef
  have hxW : x ∈ W := Submodule.subset_span ⟨0, rfl⟩
  have hfW : f ∈ W := Submodule.subset_span ⟨1, rfl⟩
  have hWrank : finrank L W = 2 := by
    rw [hWdef, finrank_span_eq_card hli, Fintype.card_fin]
  have hRefl : B.IsRefl := fun a b h => by
    rw [hB, QuadraticMap.polar_comm, ← hB, h]
  have hW : (B.restrict W).Nondegenerate := by
    refine (LinearMap.IsRefl.nondegenerate_iff_separatingLeft (B := B.restrict W)
      (fun a b h => hRefl (a : V) (b : V) h)).2 ?_
    rintro ⟨w, hw⟩ h0
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun L).1 hw
    have h1 : B (c 0 • x + c 1 • f) x = 0 := by
      have := h0 ⟨x, hxW⟩
      simpa [Fin.sum_univ_two] using this
    have h2 : B (c 0 • x + c 1 • f) f = 0 := by
      have := h0 ⟨f, hfW⟩
      simpa [Fin.sum_univ_two] using this
    rw [(hpair _ _).1] at h1
    rw [(hpair _ _).2] at h2
    apply Subtype.ext
    simp [Fin.sum_univ_two, h1, h2]
  have hcompl := isCompl_orthogonal_of_restrict_nondegenerate hRefl hW
  set W' : Submodule L V := B.orthogonal W with hW'def
  have hW' : (B.restrict W').Nondegenerate := by
    rw [restrict_nondegenerate_iff_isCompl_orthogonal hRefl, hW'def,
      orthogonal_orthogonal hN hRefl]
    exact hcompl.symm
  have hW'rank : finrank L W' = 2 * k := by
    have := Submodule.finrank_add_eq_of_isCompl hcompl
    omega
  set Q' : QuadraticForm L W' := Q.comp W'.subtype with hQ'def
  have hQ'B : QuadraticMap.polarBilin Q' = B.restrict W' :=
    LinearMap.ext₂ fun a b => rfl
  obtain ⟨v, hv0, hv⟩ := ih W' hW'rank Q' (hQ'B ▸ hW')
  have hv0' : ∀ a, Q (v a : V) = 0 := hv0
  have hv' : ∀ a b, QuadraticMap.polar Q (v a : V) (v b : V) = polarMatrix (Fin k) L a b :=
    fun a b => hv a b
  have hort : ∀ a, QuadraticMap.polar Q x (v a : V) = 0 ∧ QuadraticMap.polar Q f (v a : V) = 0 :=
    fun a => ⟨(v a).2 x hxW, (v a).2 f hfW⟩
  have hort' : ∀ a, QuadraticMap.polar Q (v a : V) x = 0 ∧ QuadraticMap.polar Q (v a : V) f = 0 :=
    fun a => ⟨by rw [QuadraticMap.polar_comm]; exact (hort a).1,
      by rw [QuadraticMap.polar_comm]; exact (hort a).2⟩
  refine ⟨Sum.elim (fun i => Fin.cases x (fun j => (v (Sum.inl j) : V)) i)
    (fun i => Fin.cases f (fun j => (v (Sum.inr j) : V)) i), ?_, ?_⟩
  · rintro (i | i) <;> cases i using Fin.cases <;> simp [hx, hf, hv0']
  have h0s : ∀ i : Fin k, (0 : Fin (k + 1)) ≠ i.succ := fun i => (Fin.succ_ne_zero i).symm
  have hs0 : ∀ i : Fin k, i.succ ≠ (0 : Fin (k + 1)) := fun i => Fin.succ_ne_zero i
  rintro (i | i) (j | j) <;> cases i using Fin.cases <;> cases j using Fin.cases <;>
    simp [polarMatrix, hxx, hxf, hfx, hff, hort, hort', hv', Matrix.one_apply, h0s, hs0]

/-- **Hyperbolic basis.** Over an algebraically closed field, a quadratic form on a space of
dimension `2 k` with nondegenerate polar form has a family of `2 k` isotropic vectors with polar
Gram matrix `[[0, 1], [1, 0]]`. -/
theorem exists_hyperbolicFamily [IsAlgClosed L] {V : Type w} [AddCommGroup V] [Module L V]
    [FiniteDimensional L V] {k : ℕ} (hV : finrank L V = 2 * k) (Q : QuadraticForm L V)
    (hN : (QuadraticMap.polarBilin Q).Nondegenerate) :
    ∃ v : Fin k ⊕ Fin k → V, (∀ a, Q (v a) = 0) ∧
      ∀ a b, QuadraticMap.polar Q (v a) (v b) = polarMatrix (Fin k) L a b :=
  exists_hyperbolicFamily_aux k V hV Q hN

/-- Entries of `P C Pᵀ` for the matrix `P` with rows `v a`. -/
theorem of_mul_mul_transpose_apply {ι n : Type*} [Fintype n] (v : ι → n → L)
    (C : Matrix n n L) (a b : ι) :
    (Matrix.of v * C * (Matrix.of v)ᵀ) a b = v a ⬝ᵥ C *ᵥ v b := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, dotProduct, mulVec,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- **Hyperbolic basis, matrix form.** Over an algebraically closed field `L` of any
characteristic, let `Q : Matrix n n L` with `Q + Qᵀ` invertible and `card n = 2 m`. Then there
is a matrix `P : Matrix (Fin m ⊕ Fin m) n L` with two-sided inverse `P'` such that
`P Q Pᵀ - formMatrix (Fin m) L` is alternating. -/
theorem exists_hyperbolic_matrix [IsAlgClosed L] {n : Type*} [Fintype n] [DecidableEq n]
    {m : ℕ} (hcard : Fintype.card n = 2 * m) (Q : Matrix n n L) (hQ : IsUnit (Q + Qᵀ)) :
    ∃ (P : Matrix (Fin m ⊕ Fin m) n L) (P' : Matrix n (Fin m ⊕ Fin m) L),
      P * P' = 1 ∧ P' * P = 1 ∧ IsAlt (P * Q * Pᵀ - formMatrix (Fin m) L) := by
  set q : QuadraticForm L (n → L) := LinearMap.BilinMap.toQuadraticMap (Matrix.toBilin' Q)
    with hqdef
  have hq : ∀ x, q x = x ⬝ᵥ Q *ᵥ x := fun x => by
    rw [hqdef, LinearMap.BilinMap.toQuadraticMap_apply, Matrix.toBilin'_apply']
  have hpolar : ∀ x y, QuadraticMap.polar q x y = x ⬝ᵥ (Q + Qᵀ) *ᵥ y := by
    intro x y
    rw [hqdef, LinearMap.BilinMap.polar_toQuadraticMap, Matrix.toBilin'_apply',
      Matrix.toBilin'_apply', Matrix.add_mulVec, dotProduct_add, Matrix.mulVec_transpose,
      dotProduct_comm x (y ᵥ* Q), ← Matrix.dotProduct_mulVec]
  have hB : QuadraticMap.polarBilin q = Matrix.toBilin' (Q + Qᵀ) :=
    LinearMap.ext₂ fun x y => by
      rw [QuadraticMap.polarBilin_apply_apply, hpolar, Matrix.toBilin'_apply']
  have hN : (QuadraticMap.polarBilin q).Nondegenerate := by
    rw [hB]
    exact nondegenerate_toBilin'_iff_det_ne_zero.2
      ((Matrix.isUnit_iff_isUnit_det _).1 hQ).ne_zero
  have hdim : finrank L (n → L) = 2 * m := by
    rw [Module.finrank_fintype_fun_eq_card, hcard]
  obtain ⟨v, hv0, hv⟩ := exists_hyperbolicFamily hdim q hN
  set P : Matrix (Fin m ⊕ Fin m) n L := Matrix.of v with hPdef
  have hPJ : P * (Q + Qᵀ) * Pᵀ = polarMatrix (Fin m) L := by
    ext a b
    rw [hPdef, of_mul_mul_transpose_apply, ← hpolar, hv]
  have hPP' : P * ((Q + Qᵀ) * Pᵀ * polarMatrix (Fin m) L) = 1 := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hPJ, polarMatrix_mul_self]
  let e : (Fin m ⊕ Fin m) ≃ n := Fintype.equivOfCardEq (by simp; omega)
  refine ⟨P, (Q + Qᵀ) * Pᵀ * polarMatrix (Fin m) L, hPP',
    (Matrix.mul_eq_one_comm_of_equiv e).1 hPP', ?_⟩
  rw [isAlt_iff]
  refine ⟨?_, fun a => ?_⟩
  · rw [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_transpose]
    have h1 : P * Q * Pᵀ - formMatrix (Fin m) L + (P * (Qᵀ * Pᵀ) - (formMatrix (Fin m) L)ᵀ) =
        P * (Q + Qᵀ) * Pᵀ - (formMatrix (Fin m) L + (formMatrix (Fin m) L)ᵀ) := by
      rw [Matrix.mul_add, Matrix.add_mul]
      simp only [Matrix.mul_assoc]
      abel
    rw [h1, hPJ, formMatrix_add_transpose, sub_self]
  · rw [Matrix.sub_apply, hPdef, of_mul_mul_transpose_apply, ← hq, hv0, formMatrix_apply]
    rcases a with a | a <;> simp

end Langlands.GroupScheme.OrthogonalMatrix
