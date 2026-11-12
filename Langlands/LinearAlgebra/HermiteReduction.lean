import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.RankNullity

/-! # Hermite reduction of integral positive definite forms

For a positive definite symmetric bilinear form `β` with integer values on a free `ℤ`-module of
rank `n`, Hermite's bound `3^(n choose 2) · min β ^ n ≤ 4^(n choose 2) · det β` holds, and `L` has
a basis whose Gram matrix has entries bounded in terms of `n` and `det β` only.
-/

noncomputable section

namespace Langlands.LinearAlgebra.Hermite

open LinearMap (BilinForm)
open Module Matrix

universe u

section Basic

variable {L : Type u} [AddCommGroup L]

/-- An integer-valued bilinear form is positive definite: `β x x > 0` for every `x ≠ 0`. -/
def IsPosDef (β : BilinForm ℤ L) : Prop := ∀ x : L, x ≠ 0 → 0 < β x x

/-- `IsPosDef β` says that the associated quadratic map `x ↦ β x x` is positive definite. -/
theorem isPosDef_iff_posDef (β : BilinForm ℤ L) :
    IsPosDef β ↔ (LinearMap.BilinMap.toQuadraticMap β).PosDef :=
  Iff.rfl

theorem IsPosDef.nonneg {β : BilinForm ℤ L} (hβ : IsPosDef β) (x : L) : 0 ≤ β x x := by
  by_cases hx : x = 0
  · simp [hx]
  · exact (hβ x hx).le

/-- The Gram determinant does not depend on the basis. -/
theorem det_toMatrix_eq {ι : Type*} [Fintype ι] [DecidableEq ι] (β : BilinForm ℤ L)
    (b c : Basis ι ℤ L) :
    (BilinForm.toMatrix c β).det = (BilinForm.toMatrix b β).det := by
  rw [← LinearMap.BilinForm.toMatrix_mul_basis_toMatrix b c, det_mul, det_mul, det_transpose]
  have h := congrArg det (b.toMatrix_mul_toMatrix_flip c)
  rw [det_mul, det_one] at h
  rcases Int.eq_one_or_neg_one_of_mul_eq_one h with h1 | h1 <;> simp [h1]

/-- A nonzero vector minimizing `β` exists as soon as `L ≠ 0`. -/
theorem exists_isMin {β : BilinForm ℤ L} (hβ : IsPosDef β) {x : L} (hx : x ≠ 0) :
    ∃ v, v ≠ 0 ∧ ∀ w, w ≠ 0 → β v v ≤ β w w := by
  classical
  have hS : ∃ n : ℕ, ∃ w, w ≠ 0 ∧ β w w = n :=
    ⟨(β x x).toNat, x, hx, (Int.toNat_of_nonneg (hβ x hx).le).symm⟩
  obtain ⟨v, hv, hvn⟩ := Nat.find_spec hS
  refine ⟨v, hv, fun w hw => ?_⟩
  have h1 := Nat.find_min' hS ⟨w, hw, (Int.toNat_of_nonneg (hβ w hw).le).symm⟩
  have h2 := Int.toNat_of_nonneg (hβ w hw).le
  rw [hvn]
  omega

theorem apply_smul_smul (β : BilinForm ℤ L) (k : ℤ) (y : L) :
    β (k • y) (k • y) = k * k * β y y := by
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

/-- A vector of minimal value is primitive in a strong sense: if `k x = m v` with `k ≠ 0`, then
`x` is an integer multiple of `v`. -/
theorem mem_span_of_smul_eq [IsTorsionFree ℤ L] {β : BilinForm ℤ L} (hβ : IsPosDef β) {v : L}
    (hv : v ≠ 0) (hmin : ∀ w, w ≠ 0 → β v v ≤ β w w) {x : L} {k m : ℤ} (hk : k ≠ 0)
    (h : k • x = m • v) : x ∈ ℤ ∙ v := by
  obtain ⟨k', m', hcop1, hk', hm'⟩ := Int.exists_gcd_one (Int.gcd_pos_of_ne_zero_left m hk)
  have hcop : IsCoprime k' m' := Int.isCoprime_iff_gcd_eq_one.2 hcop1
  have hg : (Int.gcd k m : ℤ) ≠ 0 := by
    exact_mod_cast (Int.gcd_pos_of_ne_zero_left m hk).ne'
  have h' : k' • x = m' • v := by
    have h3 : (Int.gcd k m : ℤ) • (k' • x - m' • v) = 0 := by
      rw [smul_sub, smul_smul, smul_smul, mul_comm _ k', mul_comm _ m', ← hk', ← hm', h,
        sub_self]
    exact sub_eq_zero.1 ((smul_eq_zero_iff_right hg).1 h3)
  obtain ⟨u, w, huw⟩ := hcop
  set y : L := u • v + w • x
  have hvy : v = k' • y := by
    have : k' • y = (u * k' + w * m') • v := by
      simp only [y, smul_add, add_smul]
      rw [smul_comm k' w x, h']
      simp only [smul_smul, mul_comm k' u]
    rw [this, huw, one_smul]
  have hy : y ≠ 0 := by
    rintro hy
    rw [hy, smul_zero] at hvy
    exact hv hvy
  have hk'0 : k' ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hvy
    exact hv hvy
  have hle := hmin y hy
  rw [hvy, apply_smul_smul] at hle
  have hpos := hβ y hy
  have hkk : k' * k' = 1 := by
    have h1 : k' * k' ≤ 1 := by
      by_contra hc
      have hc' := not_le.1 hc
      nlinarith
    have h2 : 0 < k' * k' := mul_self_pos.2 hk'0
    omega
  rw [Submodule.mem_span_singleton]
  refine ⟨k' * m', ?_⟩
  rw [← smul_smul, ← h', smul_smul, hkk, one_smul]

/-- The integer rounding step: `b - t a` can be made of absolute value at most `a / 2`. -/
theorem exists_abs_two_mul_sub_le (b a : ℤ) (ha : 0 < a) : ∃ t : ℤ, |2 * (b - t * a)| ≤ a := by
  have hdef : b - b / a * a = b % a := by rw [Int.emod_def]; ring
  have h0 := Int.emod_nonneg b ha.ne'
  have h1 := Int.emod_lt_of_pos b ha
  by_cases h : 2 * (b % a) ≤ a
  · refine ⟨b / a, ?_⟩
    rw [hdef, abs_le]
    constructor <;> linarith
  · refine ⟨b / a + 1, ?_⟩
    have : b - (b / a + 1) * a = b % a - a := by linarith
    rw [this, abs_le]
    constructor <;> linarith

end Basic

section Quotient

variable {L : Type u} [AddCommGroup L]

/-- The bilinear form `(x, y) ↦ β(v,v) β(x,y) - β(x,v) β(y,v)`. -/
def projForm (β : BilinForm ℤ L) (v : L) : BilinForm ℤ L :=
  β v v • β - (LinearMap.mul ℤ ℤ).compl₁₂ (β.flip v) (β.flip v)

@[simp] theorem projForm_apply (β : BilinForm ℤ L) (v x y : L) :
    projForm β v x y = β v v * β x y - β x v * β y v := by
  simp [projForm]

theorem projForm_left (β : BilinForm ℤ L) (hs : β.IsSymm) (v y : L) :
    projForm β v v y = 0 := by
  rw [projForm_apply, hs.eq v y]
  ring

theorem projForm_right (β : BilinForm ℤ L) (v x : L) : projForm β v x v = 0 := by
  rw [projForm_apply]
  ring

/-- The form `projForm β v`, descended to `L ⧸ ℤ v` in its second argument. -/
def projFormRight (β : BilinForm ℤ L) (v : L) : L →ₗ[ℤ] (L ⧸ (ℤ ∙ v)) →ₗ[ℤ] ℤ where
  toFun x := (ℤ ∙ v).liftQ (projForm β v x)
    ((Submodule.span_singleton_le_iff_mem _ _).2 (LinearMap.mem_ker.2 (projForm_right β v x)))
  map_add' x y := by
    refine Submodule.linearMap_qext _ ?_
    ext z
    simp
  map_smul' k x := by
    refine Submodule.linearMap_qext _ ?_
    ext z
    simp

/-- The form `projForm β v` on `L ⧸ ℤ v`. -/
def quotForm (β : BilinForm ℤ L) (hs : β.IsSymm) (v : L) : BilinForm ℤ (L ⧸ (ℤ ∙ v)) :=
  (ℤ ∙ v).liftQ (projFormRight β v) ((Submodule.span_singleton_le_iff_mem _ _).2
    (LinearMap.mem_ker.2 (by
    refine Submodule.linearMap_qext _ ?_
    ext z
    exact projForm_left β hs v z)))

@[simp] theorem quotForm_mk (β : BilinForm ℤ L) (hs : β.IsSymm) (v x y : L) :
    quotForm β hs v (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) =
      β v v * β x y - β x v * β y v := by
  simp [quotForm, projFormRight]

theorem quotForm_isSymm (β : BilinForm ℤ L) (hs : β.IsSymm) (v : L) :
    (quotForm β hs v).IsSymm := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [quotForm_mk, quotForm_mk, hs.eq x y]
  ring

theorem quotForm_mk_self (β : BilinForm ℤ L) (hs : β.IsSymm) (v x : L) :
    β v v * (β v v * β x x - β x v * β x v) =
      β (β v v • x - β x v • v) (β v v • x - β x v • v) := by
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [hs.eq v x]
  ring

/-- The Cauchy–Schwarz inequality `β(x,y)^2 ≤ β(x,x) β(y,y)`. -/
theorem sq_le_mul {β : BilinForm ℤ L} (hs : β.IsSymm) (hβ : IsPosDef β) (x y : L) :
    β x y ^ 2 ≤ β x x * β y y := by
  by_cases hy : y = 0
  · simp [hy]
  have hb := hβ y hy
  have h := quotForm_mk_self β hs y x
  have h0 := hβ.nonneg (β y y • x - β x y • y)
  rw [← h] at h0
  have h1 : 0 ≤ β y y * β x x - β x y * β x y := nonneg_of_mul_nonneg_right h0 hb
  rw [hs.eq x y] at h1 ⊢
  nlinarith

variable [IsTorsionFree ℤ L]

/-- For a minimal vector `v`, the quotient `L ⧸ ℤ v` is torsion-free. -/
theorem isTorsionFree_quotient {β : BilinForm ℤ L} (hβ : IsPosDef β) {v : L} (hv : v ≠ 0)
    (hmin : ∀ w, w ≠ 0 → β v v ≤ β w w) : IsTorsionFree ℤ (L ⧸ (ℤ ∙ v)) where
  isSMulRegular k hk := by
    have hk0 : k ≠ 0 := hk.ne_zero
    intro x y hxy
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    change k • Submodule.Quotient.mk x = k • Submodule.Quotient.mk y at hxy
    rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.eq,
      ← smul_sub, Submodule.mem_span_singleton] at hxy
    obtain ⟨m, hm⟩ := hxy
    rw [Submodule.Quotient.eq]
    exact mem_span_of_smul_eq hβ hv hmin hk0 hm.symm

theorem quotForm_isPosDef {β : BilinForm ℤ L} (hs : β.IsSymm) (hβ : IsPosDef β) {v : L}
    (hv : v ≠ 0) (hmin : ∀ w, w ≠ 0 → β v v ≤ β w w) : IsPosDef (quotForm β hs v) := by
  have := isTorsionFree_quotient hβ hv hmin
  intro x hx
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have ha := hβ v hv
  rw [quotForm_mk]
  have hw : β v v • x - β x v • v ≠ 0 := by
    intro h0
    apply hx
    have h1 : β v v • (Submodule.Quotient.mk x : L ⧸ (ℤ ∙ v)) = 0 := by
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, sub_eq_zero.1 h0]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
    exact (smul_eq_zero_iff_right ha.ne').1 h1
  have h2 := hβ _ hw
  rw [← quotForm_mk_self β hs v x] at h2
  exact pos_of_mul_pos_right h2 ha.le

/-- If `v ≠ 0` and the images of `y` form a basis of `L ⧸ ℤ v`, then `v, y` is a basis of
`L`. -/
def consBasis {n : ℕ} {v : L} (hv : v ≠ 0) (y : Fin n → L)
    (hy : Basis (Fin n) ℤ (L ⧸ (ℤ ∙ v)))
    (hyb : ∀ i, Submodule.Quotient.mk (y i) = hy i) : Basis (Fin (n + 1)) ℤ L :=
  Basis.mk (v := Fin.cons v y)
    (by
      rw [Fintype.linearIndependent_iff]
      intro c hc
      rw [Fin.sum_univ_succ] at hc
      simp only [Fin.cons_zero, Fin.cons_succ] at hc
      have h1 : ∑ i, c i.succ • hy i = 0 := by
        have h := congrArg (ℤ ∙ v).mkQ hc
        simp only [map_add, map_sum, map_smul, map_zero, Submodule.mkQ_apply, hyb] at h
        rwa [(Submodule.Quotient.mk_eq_zero _).2 (Submodule.mem_span_singleton_self v), smul_zero,
          zero_add] at h
      have h2 := (Fintype.linearIndependent_iff.1 hy.linearIndependent) _ h1
      have h3 : c 0 • v = 0 := by simpa [h2] using hc
      intro i
      refine Fin.cases ?_ (fun i => h2 i) i
      exact (smul_eq_zero_iff_left hv).1 h3)
    (by
      intro x _
      have hx := hy.sum_repr (Submodule.Quotient.mk x)
      have hmem : x - ∑ i, hy.repr (Submodule.Quotient.mk x) i • y i ∈ ℤ ∙ v := by
        rw [← Submodule.Quotient.eq]
        change _ = (ℤ ∙ v).mkQ _
        rw [map_sum]
        simp only [map_smul, Submodule.mkQ_apply, hyb]
        exact hx.symm
      obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.1 hmem
      have : x = k • v + ∑ i, hy.repr (Submodule.Quotient.mk x) i • y i := by
        rw [hk]; abel
      rw [this]
      refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
        (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
          (Submodule.subset_span ⟨i.succ, rfl⟩)))

theorem consBasis_zero {n : ℕ} {v : L} (hv : v ≠ 0) (y : Fin n → L)
    (hy : Basis (Fin n) ℤ (L ⧸ (ℤ ∙ v))) (hyb : ∀ i, Submodule.Quotient.mk (y i) = hy i) :
    consBasis hv y hy hyb 0 = v := by
  simp [consBasis]

theorem consBasis_succ {n : ℕ} {v : L} (hv : v ≠ 0) (y : Fin n → L)
    (hy : Basis (Fin n) ℤ (L ⧸ (ℤ ∙ v))) (hyb : ∀ i, Submodule.Quotient.mk (y i) = hy i)
    (i : Fin n) : consBasis hv y hy hyb i.succ = y i := by
  simp [consBasis]

end Quotient

section Gram

variable {L : Type u} [AddCommGroup L] [IsTorsionFree ℤ L]

/-- The Gram determinant relation `a · det β' = a ^ n · det β`, where `a = β(v,v)` and `β'` is the
form `quotForm β hs v` on `L ⧸ ℤ v`. -/
theorem mul_det_quotForm {β : BilinForm ℤ L} (hs : β.IsSymm) {n : ℕ} {v : L} (hv : v ≠ 0)
    (y : Fin n → L) (hy : Basis (Fin n) ℤ (L ⧸ (ℤ ∙ v)))
    (hyb : ∀ i, Submodule.Quotient.mk (y i) = hy i) :
    β v v * (BilinForm.toMatrix hy (quotForm β hs v)).det =
      β v v ^ n * (BilinForm.toMatrix (consBasis hv y hy hyb) β).det := by
  classical
  set a := β v v with ha
  set S := BilinForm.toMatrix (consBasis hv y hy hyb) β with hS
  have hS00 : S 0 0 = a := by
    rw [hS, BilinForm.toMatrix_apply, consBasis_zero]
  have hS0s : ∀ j, S 0 j.succ = β (y j) v := by
    intro j
    rw [hS, BilinForm.toMatrix_apply, consBasis_zero, consBasis_succ, hs.eq v (y j)]
  have hSs0 : ∀ i, S i.succ 0 = β (y i) v := by
    intro i
    rw [hS, BilinForm.toMatrix_apply, consBasis_zero, consBasis_succ]
  have hSss : ∀ i j, S i.succ j.succ = β (y i) (y j) := by
    intro i j
    rw [hS, BilinForm.toMatrix_apply, consBasis_succ, consBasis_succ]
  let E : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ := Matrix.of fun i j =>
    Fin.cases (Fin.cases 1 (fun _ => 0) j)
      (fun i' => Fin.cases (-β (y i') v) (fun j' => if i' = j' then a else 0) j) i
  have hE : E.det = a ^ n := by
    rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
    have hsub : E.submatrix Fin.succ (Fin.succAbove 0) = Matrix.diagonal fun _ => a := by
      ext i j
      simp [E, Matrix.diagonal_apply]
    simp only [Fin.succAbove_zero] at hsub
    simp [E, hsub, Matrix.det_diagonal]
  have hES0 : ∀ j, (E * S) 0 j = S 0 j := by
    intro j
    simp [E, Matrix.mul_apply, Fin.sum_univ_succ]
  have hESs : ∀ i j, (E * S) i.succ j = a * S i.succ j - β (y i) v * S 0 j := by
    intro i j
    simp [E, Matrix.mul_apply, Fin.sum_univ_succ]
    ring
  have hES : (E * S).det = a * (BilinForm.toMatrix hy (quotForm β hs v)).det := by
    rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
    have hzero : ∀ i : Fin n, (E * S) i.succ 0 = 0 := by
      intro i
      rw [hESs, hSs0, hS00]
      ring
    have hsub : (E * S).submatrix Fin.succ Fin.succ =
        BilinForm.toMatrix hy (quotForm β hs v) := by
      ext i j
      rw [Matrix.submatrix_apply, hESs, hSss, hS0s,
        BilinForm.toMatrix_apply, ← hyb, ← hyb, quotForm_mk]
    simp [hzero, hsub, hES0, hS00]
  rw [← hES, Matrix.det_mul, hE]

end Gram

section Reduction

variable {L : Type u} [AddCommGroup L]

/-- Every class in `L ⧸ ℤ v` has a representative `x` with `|2 β(x,v)| ≤ β(v,v)`. -/
theorem exists_lift {β : BilinForm ℤ L} (hβ : IsPosDef β) {v : L} (hv : v ≠ 0)
    (z : L ⧸ (ℤ ∙ v)) : ∃ x : L, Submodule.Quotient.mk x = z ∧ |2 * β x v| ≤ β v v := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  obtain ⟨t, ht⟩ := exists_abs_two_mul_sub_le (β x v) (β v v) (hβ v hv)
  refine ⟨x - t • v, ?_, ?_⟩
  · rw [Submodule.Quotient.eq]
    rw [show x - t • v - x = (-t) • v by rw [neg_smul]; abel]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
  · simpa [map_sub, map_smul] using ht

/-- For a minimal vector `v`, the values of `quotForm β hs v` on nonzero classes are at least
`3 β(v,v)^2 / 4`. -/
theorem three_mul_sq_le {β : BilinForm ℤ L} (hs : β.IsSymm) (hβ : IsPosDef β) {v : L}
    (hv : v ≠ 0) (hmin : ∀ w, w ≠ 0 → β v v ≤ β w w) (z : L ⧸ (ℤ ∙ v)) (hz : z ≠ 0) :
    3 * β v v ^ 2 ≤ 4 * quotForm β hs v z z := by
  obtain ⟨x, rfl, hx⟩ := exists_lift hβ hv z
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hz (Submodule.Quotient.mk_zero _)
  have h1 := hmin x hx0
  have ha := hβ v hv
  rw [quotForm_mk]
  have h2 : (2 * β x v) ^ 2 ≤ β v v ^ 2 := sq_le_sq' (abs_le.1 hx).1 (abs_le.1 hx).2
  nlinarith

variable [IsTorsionFree ℤ L]

theorem finrank_quotient_add_one [Module.Finite ℤ L] {v : L} (hv : v ≠ 0) :
    finrank ℤ (L ⧸ (ℤ ∙ v)) + 1 = finrank ℤ L := by
  have h1 : finrank ℤ (ℤ ∙ v) = 1 := by
    have := finrank_span_eq_card (R := ℤ) (b := fun _ : Unit => v)
      (linearIndependent_unique_iff.2 hv)
    rwa [Set.range_const, Fintype.card_unit] at this
  rw [← h1, Submodule.finrank_quotient_add_finrank]

end Reduction

/-- **Hermite's inequality**: if `p ≤ q β(x,x)` for all nonzero `x`, then
`3^(d choose 2) p^d ≤ 4^(d choose 2) q^d det β` (Platonov–Rapinchuk, Theorem 4.18 (ii)). -/
theorem hermite_bound (d : ℕ) : ∀ (L : Type u) [AddCommGroup L] (b : Basis (Fin d) ℤ L)
    (β : BilinForm ℤ L), β.IsSymm → IsPosDef β → ∀ p q : ℤ, 0 ≤ p → 0 ≤ q →
    (∀ x : L, x ≠ 0 → p ≤ q * β x x) →
    3 ^ d.choose 2 * p ^ d ≤ 4 ^ d.choose 2 * q ^ d * (BilinForm.toMatrix b β).det := by
  classical
  induction d with
  | zero =>
    intro L _ b β _ _ p q _ _ _
    simp [Matrix.det_fin_zero]
  | succ n ih =>
    intro L _ b β hs hβ p q hp hq hpq
    have : Module.Free ℤ L := Module.Free.of_basis b
    have : Module.Finite ℤ L := Module.Finite.of_basis b
    have hb0 : b 0 ≠ 0 := b.ne_zero 0
    obtain ⟨v, hv, hmin⟩ := exists_isMin hβ hb0
    set a := β v v with ha_def
    have ha : 0 < a := hβ v hv
    have := isTorsionFree_quotient hβ hv hmin
    have hrank : finrank ℤ (L ⧸ (ℤ ∙ v)) = n := by
      have h1 := finrank_quotient_add_one hv
      rw [finrank_eq_card_basis b, Fintype.card_fin] at h1
      omega
    let bN : Basis (Fin n) ℤ (L ⧸ (ℤ ∙ v)) := Module.finBasisOfFinrankEq ℤ _ hrank
    choose y hyb _ using fun i => exists_lift hβ hv (bN i)
    have key := mul_det_quotForm hs hv y bN hyb
    rw [det_toMatrix_eq β b] at key
    have h1 := ih (L ⧸ (ℤ ∙ v)) bN (quotForm β hs v) (quotForm_isSymm β hs v)
      (quotForm_isPosDef hs hβ hv hmin) (3 * a ^ 2) 4 (by positivity) (by norm_num)
      (three_mul_sq_le hs hβ hv hmin)
    set D := (BilinForm.toMatrix b β).det
    set D' := (BilinForm.toMatrix bN (quotForm β hs v)).det
    have hT : (n + 1).choose 2 = n.choose 2 + n := by
      rw [Nat.choose_succ_succ, Nat.choose_one_right, add_comm]
    have h2 : a ^ n * (3 ^ (n + 1).choose 2 * a ^ (n + 1)) ≤ a ^ n * (4 ^ (n + 1).choose 2 * D) := by
      calc a ^ n * (3 ^ (n + 1).choose 2 * a ^ (n + 1))
          = a * (3 ^ n.choose 2 * (3 * a ^ 2) ^ n) := by rw [hT]; ring
        _ ≤ a * (4 ^ n.choose 2 * 4 ^ n * D') := mul_le_mul_of_nonneg_left h1 ha.le
        _ = 4 ^ (n + 1).choose 2 * (a * D') := by rw [hT]; ring
        _ = a ^ n * (4 ^ (n + 1).choose 2 * D) := by rw [key]; ring
    have h3 : 3 ^ (n + 1).choose 2 * a ^ (n + 1) ≤ 4 ^ (n + 1).choose 2 * D :=
      le_of_mul_le_mul_left h2 (pow_pos ha n)
    have h4 : p ^ (n + 1) ≤ q ^ (n + 1) * a ^ (n + 1) := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ hp (hpq v hv) _
    calc 3 ^ (n + 1).choose 2 * p ^ (n + 1)
        ≤ 3 ^ (n + 1).choose 2 * (q ^ (n + 1) * a ^ (n + 1)) :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = q ^ (n + 1) * (3 ^ (n + 1).choose 2 * a ^ (n + 1)) := by ring
      _ ≤ q ^ (n + 1) * (4 ^ (n + 1).choose 2 * D) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = 4 ^ (n + 1).choose 2 * q ^ (n + 1) * D := by ring

/-- The Gram determinant of an integral positive definite form is positive. -/
theorem det_pos {d : ℕ} {L : Type u} [AddCommGroup L] (b : Basis (Fin d) ℤ L)
    {β : BilinForm ℤ L} (hs : β.IsSymm) (hβ : IsPosDef β) :
    0 < (BilinForm.toMatrix b β).det := by
  have h := hermite_bound d L b β hs hβ 1 1 zero_le_one zero_le_one
    (fun x hx => by have := hβ x hx; rw [one_mul]; omega)
  simp only [one_pow, mul_one] at h
  have h3 : 0 < (3 : ℤ) ^ d.choose 2 := by positivity
  have h4 : 0 < (4 : ℤ) ^ d.choose 2 := by positivity
  by_contra hc
  have := mul_nonpos_of_nonneg_of_nonpos h4.le (not_lt.1 hc)
  linarith

/-- **Reduction**: for each rank `n` and bound `Δ`, there is `C` such that every integral positive
definite symmetric form of rank `n` with Gram determinant at most `Δ` has a basis whose Gram
matrix has entries of absolute value at most `C`. -/
theorem exists_reduced_basis (n : ℕ) (Δ : ℤ) : ∃ C : ℤ, ∀ (L : Type u) [AddCommGroup L]
    (b : Basis (Fin n) ℤ L) (β : BilinForm ℤ L), β.IsSymm → IsPosDef β →
    (BilinForm.toMatrix b β).det ≤ Δ →
    ∃ c : Basis (Fin n) ℤ L, ∀ i j, |β (c i) (c j)| ≤ C := by
  classical
  induction n generalizing Δ with
  | zero =>
    exact ⟨0, fun L _ b β _ _ _ => ⟨b, fun i => Fin.elim0 i⟩⟩
  | succ n ih =>
    set A : ℤ := 4 ^ (n + 1).choose 2 * Δ
    obtain ⟨C', hC'⟩ := ih (A ^ n * Δ)
    refine ⟨|C'| + A * A + A, fun L _ b β hs hβ hΔ => ?_⟩
    have : Module.Free ℤ L := Module.Free.of_basis b
    have : Module.Finite ℤ L := Module.Finite.of_basis b
    obtain ⟨v, hv, hmin⟩ := exists_isMin hβ (b.ne_zero 0)
    set a := β v v with ha_def
    have ha : 0 < a := hβ v hv
    have := isTorsionFree_quotient hβ hv hmin
    have hrank : finrank ℤ (L ⧸ (ℤ ∙ v)) = n := by
      have h1 := finrank_quotient_add_one hv
      rw [finrank_eq_card_basis b, Fintype.card_fin] at h1
      omega
    let bN : Basis (Fin n) ℤ (L ⧸ (ℤ ∙ v)) := Module.finBasisOfFinrankEq ℤ _ hrank
    set D := (BilinForm.toMatrix b β).det
    have hD := det_pos b hs hβ
    -- the minimum is bounded by Hermite's inequality
    have haA : a ≤ A := by
      have h := hermite_bound (n + 1) L b β hs hβ a 1 ha.le zero_le_one
        (fun x hx => by simpa using hmin x hx)
      simp only [one_pow, mul_one] at h
      have h1 : a ≤ a ^ (n + 1) := by
        calc a = a ^ 1 := (pow_one a).symm
          _ ≤ a ^ (n + 1) := pow_le_pow_right₀ (by omega) (by omega)
      have h2 : a ^ (n + 1) ≤ 3 ^ (n + 1).choose 2 * a ^ (n + 1) :=
        le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by norm_num))
      calc a ≤ 4 ^ (n + 1).choose 2 * D := h1.trans (h2.trans h)
        _ ≤ A := mul_le_mul_of_nonneg_left hΔ (by positivity)
    -- the determinant of the quotient form is bounded
    choose y0 hyb0 _ using fun i => exists_lift hβ hv (bN i)
    have key := mul_det_quotForm hs hv y0 bN hyb0
    rw [det_toMatrix_eq β b] at key
    set D' := (BilinForm.toMatrix bN (quotForm β hs v)).det
    have hD' := det_pos bN (quotForm_isSymm β hs v) (quotForm_isPosDef hs hβ hv hmin)
    have hD'Δ : D' ≤ A ^ n * Δ := by
      calc D' ≤ a * D' := le_mul_of_one_le_left hD'.le ha
        _ = a ^ n * D := key
        _ ≤ A ^ n * Δ := mul_le_mul (pow_le_pow_left₀ ha.le haA n) hΔ hD.le
            (pow_nonneg (ha.le.trans haA) n)
    obtain ⟨c', hc'⟩ := hC' (L ⧸ (ℤ ∙ v)) bN (quotForm β hs v) (quotForm_isSymm β hs v)
      (quotForm_isPosDef hs hβ hv hmin) hD'Δ
    choose y hyb hy using fun i => exists_lift hβ hv (c' i)
    have hA0 : 0 ≤ A := ha.le.trans haA
    have hyv : ∀ i, |β (y i) v| ≤ A := by
      intro i
      have := hy i
      rw [abs_mul, abs_two] at this
      have : |β (y i) v| ≤ a := by linarith [abs_nonneg (β (y i) v)]
      exact this.trans haA
    refine ⟨consBasis hv y c' hyb, fun i j => ?_⟩
    have hC0 : 0 ≤ |C'| + A * A := by positivity
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
      simp only [consBasis_zero, consBasis_succ]
    · rw [abs_of_pos ha]
      linarith
    · rw [hs.eq v (y j)]
      have := hyv j
      linarith
    · have := hyv i
      linarith
    · have h1 := hc' i j
      rw [← hyb i, ← hyb j, quotForm_mk] at h1
      have h2 : |β (y i) (y j)| ≤ |a * β (y i) (y j)| := by
        rw [abs_mul, abs_of_pos ha]
        exact le_mul_of_one_le_left (abs_nonneg _) ha
      have h3 : |β (y i) v * β (y j) v| ≤ A * A := by
        rw [abs_mul]
        exact mul_le_mul (hyv i) (hyv j) (abs_nonneg _) hA0
      have h4 : |a * β (y i) (y j)| ≤ |C'| + A * A := by
        have : a * β (y i) (y j) = (a * β (y i) (y j) - β (y i) v * β (y j) v) +
            β (y i) v * β (y j) v := by ring
        rw [this]
        exact (abs_add_le _ _).trans (add_le_add (h1.trans (le_abs_self C')) h3)
      linarith

end Langlands.LinearAlgebra.Hermite
