import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.RingDivision

/-!
# A dimension count for divisibility by a bivariate polynomial

Let `fh : F[X][Y]` be nonzero of `Y`-degree `n`, with all coefficients of `X`-degree at most `m`.
For a finite family of `F`-linear maps `φ l : V → F[X][Y]` landing in the boxes
`{p | deg_Y p ≤ b l, deg_X (coefficients of p) ≤ a l}`, if
`∑ l, (n (a l + 1) + m (b l + 1 - n)) < dim V` then some nonzero `v` has `fh ∣ φ l v` for all `l`.

The proof compares the dimensions of the source and target of the linear map
`(v, (q l)_l) ↦ (box coefficients of φ l v - fh * q l)_l`, where `q l` runs over the box of
bidegree `(a l - m, b l - n)`.
-/

open Polynomial Module

universe u

namespace Langlands.AlgebraicGeometry.LangWeil.Stepanov

section Box

variable {R : Type*} [CommRing R]

/-- Box bounds add under multiplication. -/
theorem box_mul {p q : Polynomial (Polynomial R)} {a₁ b₁ a₂ b₂ : ℕ}
    (hp : p.natDegree ≤ b₁ ∧ ∀ i, (p.coeff i).natDegree ≤ a₁)
    (hq : q.natDegree ≤ b₂ ∧ ∀ i, (q.coeff i).natDegree ≤ a₂) :
    (p * q).natDegree ≤ b₁ + b₂ ∧ ∀ i, ((p * q).coeff i).natDegree ≤ a₁ + a₂ := by
  refine ⟨natDegree_mul_le.trans (add_le_add hp.1 hq.1), fun i => ?_⟩
  rw [coeff_mul]
  exact natDegree_sum_le_of_forall_le _ _
    (fun x _ => natDegree_mul_le.trans (add_le_add (hp.2 _) (hq.2 _)))

/-- Boxes are closed under subtraction. -/
theorem box_sub {p q : Polynomial (Polynomial R)} {a b : ℕ}
    (hp : p.natDegree ≤ b ∧ ∀ i, (p.coeff i).natDegree ≤ a)
    (hq : q.natDegree ≤ b ∧ ∀ i, (q.coeff i).natDegree ≤ a) :
    (p - q).natDegree ≤ b ∧ ∀ i, ((p - q).coeff i).natDegree ≤ a :=
  ⟨(natDegree_sub_le _ _).trans (max_le hp.1 hq.1), fun i => by
    rw [coeff_sub]; exact (natDegree_sub_le _ _).trans (max_le (hp.2 i) (hq.2 i))⟩

/-- Boxes are closed under finite sums. -/
theorem box_sum {α : Type*} (s : Finset α) (f : α → Polynomial (Polynomial R)) {a b : ℕ}
    (h : ∀ x ∈ s, (f x).natDegree ≤ b ∧ ∀ i, ((f x).coeff i).natDegree ≤ a) :
    (∑ x ∈ s, f x).natDegree ≤ b ∧ ∀ i, ((∑ x ∈ s, f x).coeff i).natDegree ≤ a :=
  ⟨natDegree_sum_le_of_forall_le _ _ fun x hx => (h x hx).1, fun i => by
    rw [finsetSum_coeff]; exact natDegree_sum_le_of_forall_le _ _ fun x hx => (h x hx).2 i⟩

/-- The box of a bivariate monomial. -/
theorem box_monomial (i j : ℕ) (c : R) :
    (monomial i (monomial j c)).natDegree ≤ i ∧
      ∀ k, ((monomial i (monomial j c) : Polynomial (Polynomial R)).coeff k).natDegree ≤ j := by
  refine ⟨natDegree_monomial_le _, fun k => ?_⟩
  rw [coeff_monomial]
  split_ifs
  · exact natDegree_monomial_le _
  · simp

/-- A polynomial in the box `(a, b)` whose coefficients in the box all vanish is zero. -/
theorem eq_zero_of_box {p : Polynomial (Polynomial R)} {a b : ℕ}
    (hp : p.natDegree ≤ b ∧ ∀ i, (p.coeff i).natDegree ≤ a)
    (h : ∀ i j, i ≤ b → j ≤ a → (p.coeff i).coeff j = 0) : p = 0 := by
  ext i j
  simp only [coeff_zero]
  by_cases hi : i ≤ b
  · by_cases hj : j ≤ a
    · exact h i j hi hj
    · exact coeff_eq_zero_of_natDegree_lt ((hp.2 i).trans_lt (not_le.mp hj))
  · rw [coeff_eq_zero_of_natDegree_lt (hp.1.trans_lt (not_le.mp hi)), coeff_zero]

end Box

/-- The counting inequality: the box `(a, b)` has dimension at most the codimension bound
`n (a + 1) + m (b + 1 - n)` plus the dimension of the box `(a - m, b - n)`. -/
theorem box_count_le (n m a b : ℕ) :
    (b + 1) * (a + 1) ≤ n * (a + 1) + m * (b + 1 - n) + (b + 1 - n) * (a + 1 - m) := by
  rcases le_or_gt (b + 1) n with h | h
  · rw [Nat.sub_eq_zero_of_le h]
    simp only [mul_zero, zero_mul, add_zero]
    exact Nat.mul_le_mul_right _ h
  · obtain ⟨k, hk⟩ : ∃ k, b + 1 = n + k := ⟨b + 1 - n, by omega⟩
    rw [hk, Nat.add_sub_cancel_left]
    rcases le_or_gt (a + 1) m with h' | h'
    · rw [Nat.sub_eq_zero_of_le h']
      have := Nat.mul_le_mul_left k h'
      nlinarith
    · obtain ⟨j, hj⟩ : ∃ j, a + 1 = m + j := ⟨a + 1 - m, by omega⟩
      rw [hj, Nat.add_sub_cancel_left]
      exact le_of_eq (by ring)

variable (F : Type u) [Field F]

/-- The coefficient array of a bivariate polynomial on the box `[0, B) × [0, A)`
(`Y`-exponent first). -/
noncomputable def boxCoeff (B A : ℕ) : Polynomial (Polynomial F) →ₗ[F] (Fin B × Fin A → F) where
  toFun p k := (p.coeff k.1).coeff k.2
  map_add' p q := by ext k; simp
  map_smul' c p := by ext k; simp

theorem boxCoeff_apply (B A : ℕ) (p : Polynomial (Polynomial F)) (k : Fin B × Fin A) :
    boxCoeff F B A p k = (p.coeff k.1).coeff k.2 := rfl

/-- The bivariate polynomial with a given coefficient array on the box `[0, B) × [0, A)`. -/
noncomputable def boxEncode (B A : ℕ) : (Fin B × Fin A → F) →ₗ[F] Polynomial (Polynomial F) where
  toFun q := ∑ k : Fin B × Fin A, monomial (k.1 : ℕ) (monomial (k.2 : ℕ) (q k))
  map_add' q r := by simp [Finset.sum_add_distrib]
  map_smul' c q := by simp [Finset.smul_sum, smul_monomial]

theorem boxEncode_apply (B A : ℕ) (q : Fin B × Fin A → F) :
    boxEncode F B A q = ∑ k : Fin B × Fin A, monomial (k.1 : ℕ) (monomial (k.2 : ℕ) (q k)) :=
  rfl

/-- The encoding recovers its coefficient array. -/
theorem boxEncode_coeff (B A : ℕ) (q : Fin B × Fin A → F) (i : Fin B) (j : Fin A) :
    ((boxEncode F B A q).coeff i).coeff j = q (i, j) := by
  classical
  rw [boxEncode_apply, finsetSum_coeff, finsetSum_coeff,
    Finset.sum_eq_single (i, j)]
  · simp
  · intro k _ hk
    rw [coeff_monomial]
    split_ifs with h1
    · rw [coeff_monomial]
      split_ifs with h2
      · exact absurd (Prod.ext (Fin.ext h1) (Fin.ext h2)) hk
      · rfl
    · rfl
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- Multiplication by `fh` after encoding. -/
noncomputable def boxMulEncode (fh : Polynomial (Polynomial F)) (B A : ℕ) :
    (Fin B × Fin A → F) →ₗ[F] Polynomial (Polynomial F) :=
  LinearMap.mulLeft F fh ∘ₗ boxEncode F B A

theorem boxMulEncode_apply (fh : Polynomial (Polynomial F)) (B A : ℕ) (q : Fin B × Fin A → F) :
    boxMulEncode F fh B A q = fh * boxEncode F B A q := rfl

/-- `fh` times an element of the box `(a - m, b - n)` lies in the box `(a, b)`. -/
theorem box_mul_boxEncode (fh : Polynomial (Polynomial F)) {n m a b : ℕ}
    (hn : fh.natDegree ≤ n) (hm : ∀ i, (fh.coeff i).natDegree ≤ m)
    (q : Fin (b + 1 - n) × Fin (a + 1 - m) → F) :
    (fh * boxEncode F (b + 1 - n) (a + 1 - m) q).natDegree ≤ b ∧
      ∀ i, ((fh * boxEncode F (b + 1 - n) (a + 1 - m) q).coeff i).natDegree ≤ a := by
  rw [boxEncode_apply, Finset.mul_sum]
  refine box_sum _ _ fun k _ => ?_
  have hk1 := k.1.isLt
  have hk2 := k.2.isLt
  obtain ⟨h1, h2⟩ := box_mul ⟨hn, hm⟩ (box_monomial (k.1 : ℕ) (k.2 : ℕ) (q k))
  exact ⟨h1.trans (by omega), fun i => (h2 i).trans (by omega)⟩

/-- The linear map `(v, (q l)_l) ↦ (box coefficients of φ l v - fh * q l)_l` whose kernel
produces the divisible vector. -/
noncomputable def kernelMap (fh : Polynomial (Polynomial F)) (m n : ℕ)
    (V : Type u) [AddCommGroup V] [Module F V]
    (ι : Type) (φ : ι → V →ₗ[F] Polynomial (Polynomial F)) (a b : ι → ℕ) :
    (V × ((l : ι) → (Fin (b l + 1 - n) × Fin (a l + 1 - m) → F))) →ₗ[F]
      ((l : ι) → (Fin (b l + 1) × Fin (a l + 1) → F)) :=
  LinearMap.pi fun l => (boxCoeff F (b l + 1) (a l + 1)).comp
    ((φ l).comp (LinearMap.fst F V _) -
      (boxMulEncode F fh (b l + 1 - n) (a l + 1 - m)).comp
        ((LinearMap.proj l).comp (LinearMap.snd F V _)))

theorem kernelMap_apply (fh : Polynomial (Polynomial F)) (m n : ℕ)
    (V : Type u) [AddCommGroup V] [Module F V]
    (ι : Type) (φ : ι → V →ₗ[F] Polynomial (Polynomial F)) (a b : ι → ℕ) (v : V)
    (q : (l : ι) → (Fin (b l + 1 - n) × Fin (a l + 1 - m) → F)) (l : ι) :
    kernelMap F fh m n V ι φ a b (v, q) l =
      boxCoeff F (b l + 1) (a l + 1)
        (φ l v - fh * boxEncode F (b l + 1 - n) (a l + 1 - m) (q l)) := rfl

/-- **Divisible kernel.** Let `fh : F[X][Y]` be nonzero, of `Y`-degree `n`, with coefficients of
`X`-degree at most `m`, and let `φ l : V → F[X][Y]` (`l : ι`) be `F`-linear maps into the boxes
of bidegree `(a l, b l)`. If `∑ l, (n (a l + 1) + m (b l + 1 - n)) < dim V`, then some nonzero
`v : V` has `fh ∣ φ l v` for every `l`. -/
theorem exists_ne_zero_forall_dvd (F : Type u) [Field F] (fh : Polynomial (Polynomial F))
    (m : ℕ) (hfh : fh ≠ 0) (hm : ∀ i, (fh.coeff i).natDegree ≤ m)
    (V : Type u) [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ι : Type) [Fintype ι] (φ : ι → V →ₗ[F] Polynomial (Polynomial F)) (a b : ι → ℕ)
    (hφ : ∀ l v, (φ l v).natDegree ≤ b l ∧ ∀ i, ((φ l v).coeff i).natDegree ≤ a l)
    (hdim : ∑ l, (fh.natDegree * (a l + 1) + m * (b l + 1 - fh.natDegree)) <
      Module.finrank F V) :
    ∃ v : V, v ≠ 0 ∧ ∀ l, fh ∣ φ l v := by
  classical
  obtain ⟨n, hn⟩ : ∃ n, fh.natDegree = n := ⟨_, rfl⟩
  rw [hn] at hdim
  have hlt : finrank F ((l : ι) → (Fin (b l + 1) × Fin (a l + 1) → F)) <
      finrank F (V × ((l : ι) → (Fin (b l + 1 - n) × Fin (a l + 1 - m) → F))) := by
    rw [finrank_prod, finrank_pi_fintype, finrank_pi_fintype]
    simp only [finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin]
    calc ∑ l, (b l + 1) * (a l + 1)
        ≤ ∑ l, ((n * (a l + 1) + m * (b l + 1 - n)) + (b l + 1 - n) * (a l + 1 - m)) :=
          Finset.sum_le_sum fun l _ => box_count_le n m (a l) (b l)
      _ = ∑ l, (n * (a l + 1) + m * (b l + 1 - n)) +
            ∑ l, (b l + 1 - n) * (a l + 1 - m) := Finset.sum_add_distrib
      _ < finrank F V + ∑ l, (b l + 1 - n) * (a l + 1 - m) := Nat.add_lt_add_right hdim _
  obtain ⟨⟨v, q⟩, hker, hne⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot
      (LinearMap.ker_ne_bot_of_finrank_lt (f := kernelMap F fh m n V ι φ a b) hlt)
  rw [LinearMap.mem_ker] at hker
  have key : ∀ l, φ l v = fh * boxEncode F (b l + 1 - n) (a l + 1 - m) (q l) := by
    intro l
    have h := congrFun hker l
    rw [kernelMap_apply] at h
    refine sub_eq_zero.mp (eq_zero_of_box
      (box_sub (hφ l v) (box_mul_boxEncode F fh hn.le hm (q l))) fun i j hi hj => ?_)
    have := congrFun h (⟨i, by omega⟩, ⟨j, by omega⟩)
    simpa [boxCoeff_apply] using this
  refine ⟨v, fun hv => hne ?_, fun l => ⟨_, key l⟩⟩
  subst hv
  have hq : q = 0 := by
    funext l k
    have h0 := key l
    rw [map_zero, eq_comm, mul_eq_zero] at h0
    have h1 := boxEncode_coeff F _ _ (q l) k.1 k.2
    rw [h0.resolve_left hfh] at h1
    simpa using h1.symm
  rw [hq]
  rfl

end Langlands.AlgebraicGeometry.LangWeil.Stepanov
