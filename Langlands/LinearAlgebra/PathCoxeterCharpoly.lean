import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.LinearCombination

/-! # Characteristic polynomials of path Coxeter products -/

noncomputable section

open Polynomial Matrix

namespace Langlands.LinearAlgebra.PathCoxeter

variable {R : Type*} [CommRing R] {n : ℕ}

/-! ### Coordinates indexed by natural numbers -/

/-- The coordinate of a vector at a natural index, with value `0` outside the range. -/
def vget (v : Fin n → R) (j : ℕ) : R := if h : j < n then v ⟨j, h⟩ else 0

@[simp] theorem vget_fin (v : Fin n → R) (a : Fin n) : vget v a = v a := by
  simp [vget, a.2]

theorem vget_of_lt (v : Fin n → R) {j : ℕ} (h : j < n) : vget v j = v ⟨j, h⟩ := by
  simp [vget, h]

theorem vget_of_le (v : Fin n → R) {j : ℕ} (h : n ≤ j) : vget v j = 0 := by
  simp [vget, show ¬ j < n by omega]

theorem vget_add (v w : Fin n → R) : vget (v + w) = vget v + vget w := by
  funext j; by_cases h : j < n <;> simp [vget, h]

theorem vget_smul (r : R) (v : Fin n → R) : vget (r • v) = r • vget v := by
  funext j; by_cases h : j < n <;> simp [vget, h]

theorem vget_single (b : Fin n) (j : ℕ) :
    vget (Pi.single b (1 : R)) j = if j = (b : ℕ) then 1 else 0 := by
  by_cases h : j < n
  · rw [vget_of_lt _ h, Pi.single_apply]
    simp [Fin.ext_iff]
  · rw [vget_of_le _ (by omega), ite_eq_right (by have := b.2; omega)]

theorem vget_injective : Function.Injective (vget (R := R) (n := n)) := by
  intro v w h
  funext a
  have := congrFun h a
  simpa using this

/-! ### Actions on families indexed by natural numbers -/

/-- The action of the simple factor on the lines `i, i + 1`. -/
def sfacAct (i : ℕ) (c : R) (f : ℕ → R) : ℕ → R := fun b =>
  if b = i then -c * f i + f (i + 1) else if b = i + 1 then -f i else f b

/-- The action of a `3 × 3` block `β` on the lines `j, j + 1, j + 2`. -/
def coreAct (j : ℕ) (β : ℕ → ℕ → R) (f : ℕ → R) : ℕ → R := fun b =>
  if j ≤ b ∧ b < j + 3 then
    β (b - j) 0 * f j + β (b - j) 1 * f (j + 1) + β (b - j) 2 * f (j + 2)
  else f b

/-- The action of the product of `k` consecutive simple factors starting at the line `a`. -/
def pprodAct (a k : ℕ) (c : ℕ → R) (f : ℕ → R) : ℕ → R := fun b =>
  if b = a then (∑ i ∈ Finset.range k, -c (a + i) * f (a + i)) + f (a + k)
  else if a < b ∧ b ≤ a + k then -f (b - 1) else f b

theorem pprodAct_zero (a : ℕ) (c : ℕ → R) (f : ℕ → R) : pprodAct a 0 c f = f := by
  funext b
  unfold pprodAct
  by_cases h : b = a
  · subst h; simp
  · rw [ite_eq_right h, ite_eq_right (by omega)]

theorem pprodAct_succ (a k : ℕ) (c : ℕ → R) (f : ℕ → R) :
    pprodAct a (k + 1) c f = pprodAct a k c (sfacAct (a + k) (c (a + k)) f) := by
  funext b
  unfold pprodAct sfacAct
  by_cases hb : b = a
  · subst hb
    simp only [ite_true, Finset.sum_range_succ]
    have hs : ∀ i ∈ Finset.range k, -c (b + i) *
        (if b + i = b + k then -c (b + k) * f (b + k) + f (b + k + 1)
          else if b + i = b + k + 1 then -f (b + k) else f (b + i)) =
        -c (b + i) * f (b + i) := by
      intro i hi
      rw [Finset.mem_range] at hi
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    rw [Finset.sum_congr rfl hs, show b + (k + 1) = b + k + 1 by omega]
    ring
  · rw [ite_eq_right hb, ite_eq_right hb]
    by_cases h1 : a < b ∧ b ≤ a + k
    · rw [ite_eq_left (by omega), ite_eq_left h1, ite_eq_right (by omega), ite_eq_right (by omega)]
    · rw [ite_eq_right h1]
      by_cases h2 : b = a + k + 1
      · rw [ite_eq_left (by omega), ite_eq_right (by omega), ite_eq_left h2, h2]
        simp
      · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right h2]

/-! ### Matrices -/

/-- The simple factor on the lines `i` and `i + 1`: its columns are
`e_i ↦ -c e_i - e_(i+1)` and `e_(i+1) ↦ e_i`, and it fixes every other basis vector. -/
def sfac (n : ℕ) (i : ℕ) (c : R) : Matrix (Fin n) (Fin n) R :=
  fun a b =>
    if (b : ℕ) = i then (if (a : ℕ) = i then -c else if (a : ℕ) = i + 1 then -1 else 0)
    else if (b : ℕ) = i + 1 then (if (a : ℕ) = i then 1 else 0)
    else if a = b then 1 else 0

theorem sfac_mulVec_apply {i : ℕ} (hi : i + 1 < n) (c : R) (v : Fin n → R) (a : Fin n) :
    (sfac n i c *ᵥ v) a =
      if (a : ℕ) = i then -c * vget v i + vget v (i + 1)
      else if (a : ℕ) = i + 1 then -vget v i else v a := by
  rw [mulVec, dotProduct]
  have hsplit : ∀ b : Fin n, sfac n i c a b * v b =
      (if (b : ℕ) = i then (if (a : ℕ) = i then -c else if (a : ℕ) = i + 1 then -1 else 0) *
          vget v i else 0) +
        (if (b : ℕ) = i + 1 then (if (a : ℕ) = i then 1 else 0) * vget v (i + 1) else 0) +
        (if (b : ℕ) ≠ i ∧ (b : ℕ) ≠ i + 1 ∧ a = b then v b else 0) := by
    intro b
    unfold sfac
    by_cases h1 : (b : ℕ) = i
    · have : vget v i = v b := by rw [← h1, vget_fin]
      simp [h1, this]
    · by_cases h2 : (b : ℕ) = i + 1
      · have : vget v (i + 1) = v b := by rw [← h2, vget_fin]
        simp [h2, this]
      · by_cases h3 : a = b <;> simp [h1, h2, h3]
  simp only [hsplit, Finset.sum_add_distrib]
  rw [Finset.sum_ite, Finset.sum_ite, Finset.sum_ite]
  simp only [Finset.sum_const_zero, add_zero]
  have hi' : i < n := by omega
  have e1 : (Finset.univ.filter fun b : Fin n => (b : ℕ) = i) = {⟨i, hi'⟩} := by
    ext b; simp [Fin.ext_iff]
  have e2 : (Finset.univ.filter fun b : Fin n => (b : ℕ) = i + 1) = {⟨i + 1, hi⟩} := by
    ext b; simp [Fin.ext_iff]
  rw [e1, e2, Finset.sum_singleton, Finset.sum_singleton]
  by_cases ha1 : (a : ℕ) = i
  · have e3 : (Finset.univ.filter fun b : Fin n =>
        (b : ℕ) ≠ i ∧ (b : ℕ) ≠ i + 1 ∧ a = b) = ∅ := by
      ext b; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
        iff_false]
      rintro ⟨hb1, -, rfl⟩
      exact hb1 ha1
    simp [ha1, e3]
  · by_cases ha2 : (a : ℕ) = i + 1
    · have e3 : (Finset.univ.filter fun b : Fin n =>
          (b : ℕ) ≠ i ∧ (b : ℕ) ≠ i + 1 ∧ a = b) = ∅ := by
        ext b; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
          iff_false]
        rintro ⟨-, hb2, rfl⟩
        exact hb2 ha2
      simp [ha2, e3]
    · have e3 : (Finset.univ.filter fun b : Fin n =>
          (b : ℕ) ≠ i ∧ (b : ℕ) ≠ i + 1 ∧ a = b) = {a} := by
        ext b; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
        constructor
        · rintro ⟨-, -, rfl⟩; rfl
        · rintro rfl; exact ⟨ha1, ha2, rfl⟩
      simp [ha1, ha2, e3]

theorem vget_sfac_mulVec {i : ℕ} (hi : i + 1 < n) (c : R) (v : Fin n → R) :
    vget (sfac n i c *ᵥ v) = sfacAct i c (vget v) := by
  funext b
  by_cases hb : b < n
  · rw [vget_of_lt _ hb, sfac_mulVec_apply hi]
    simp only [sfacAct]
    split_ifs <;> simp [vget_of_lt _ hb]
  · rw [vget_of_le _ (by omega)]
    simp only [sfacAct]
    rw [ite_eq_right (by omega), ite_eq_right (by omega), vget_of_le _ (by omega)]

theorem sfac_map {S : Type*} [CommRing S] (φ : R →+* S) (i : ℕ) (c : R) :
    (sfac n i c).map φ = sfac n i (φ c) := by
  ext a b
  simp only [sfac, map_apply]
  split_ifs <;> simp

/-- The product of `k` consecutive simple factors starting at the line `a`, in increasing
order of the lines. -/
def pprod (n a k : ℕ) (c : ℕ → R) : Matrix (Fin n) (Fin n) R :=
  ((List.range k).map fun i => sfac n (a + i) (c (a + i))).prod

theorem pprod_zero (a : ℕ) (c : ℕ → R) : pprod n a 0 c = 1 := by
  simp [pprod]

theorem pprod_succ (a k : ℕ) (c : ℕ → R) :
    pprod n a (k + 1) c = pprod n a k c * sfac n (a + k) (c (a + k)) := by
  simp [pprod, List.range_succ, List.prod_append]

theorem vget_pprod_mulVec {a k : ℕ} (h : a + k < n) (c : ℕ → R) (v : Fin n → R) :
    vget (pprod n a k c *ᵥ v) = pprodAct a k c (vget v) := by
  induction k generalizing v with
  | zero => rw [pprod_zero, one_mulVec, pprodAct_zero]
  | succ k ih =>
    rw [pprod_succ, ← mulVec_mulVec, ih (by omega), vget_sfac_mulVec (by omega),
      pprodAct_succ]

theorem pprod_map {S : Type*} [CommRing S] (φ : R →+* S) (a k : ℕ) (c : ℕ → R) :
    (pprod n a k c).map φ = pprod n a k (fun i => φ (c i)) := by
  change φ.mapMatrix (pprod n a k c) = _
  rw [pprod, map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  exact sfac_map φ _ _

/-- The linear map of a `3 × 3` block `β` on the lines `j, j + 1, j + 2`. -/
def coreLin (n j : ℕ) (β : ℕ → ℕ → R) : (Fin n → R) →ₗ[R] (Fin n → R) where
  toFun v b := coreAct j β (vget v) b
  map_add' v w := by
    funext b
    simp only [vget_add, coreAct, Pi.add_apply]
    split_ifs <;> ring
  map_smul' r v := by
    funext b
    simp only [vget_smul, coreAct, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> ring

/-- The matrix of a `3 × 3` block `β` on the lines `j, j + 1, j + 2`, the identity elsewhere. -/
def core (n j : ℕ) (β : ℕ → ℕ → R) : Matrix (Fin n) (Fin n) R :=
  LinearMap.toMatrix' (coreLin n j β)

theorem vget_core_mulVec {j : ℕ} (h : j + 3 ≤ n) (β : ℕ → ℕ → R) (v : Fin n → R) :
    vget (core n j β *ᵥ v) = coreAct j β (vget v) := by
  rw [core, LinearMap.toMatrix'_mulVec]
  funext b
  by_cases hb : b < n
  · rw [vget_of_lt _ hb]
    rfl
  · rw [vget_of_le _ (by omega)]
    simp only [coreAct]
    rw [ite_eq_right (by omega), vget_of_le _ (by omega)]

theorem core_apply (j : ℕ) (β : ℕ → ℕ → R) (a b : Fin n) :
    core n j β a b = coreAct j β (fun i => if i = (b : ℕ) then 1 else 0) a := by
  rw [core, LinearMap.toMatrix'_apply]
  change coreAct j β (vget (Pi.single b 1)) a = _
  congr 1
  funext i
  exact vget_single b i

theorem core_map {S : Type*} [CommRing S] (φ : R →+* S) (j : ℕ) (β : ℕ → ℕ → R) :
    (core n j β).map φ = core n j (fun a b => φ (β a b)) := by
  ext a b
  rw [map_apply, core_apply, core_apply]
  simp only [coreAct]
  split_ifs <;> simp

/-! ### Cramer's rule for the first coordinate -/

theorem mul_det_eq_of_mulVec {N : ℕ} {S : Type*} [CommRing S]
    (A : Matrix (Fin (N + 1)) (Fin (N + 1)) S) (x : Fin (N + 1) → S) (p : S)
    (hx : A *ᵥ x = Pi.single 0 p) :
    x 0 * A.det = p * (A.submatrix Fin.succ Fin.succ).det := by
  have h1 : (adjugate A * A) *ᵥ x = A.det • x := by
    rw [adjugate_mul, smul_mulVec, one_mulVec]
  rw [← mulVec_mulVec, hx] at h1
  have h2 := congrFun h1 0
  rw [mulVec_single, Pi.smul_apply, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op,
    col_apply, Pi.smul_apply, smul_eq_mul, adjugate_fin_succ_eq_det_submatrix] at h2
  simp only [Fin.val_zero, add_zero, pow_zero, one_mul, Fin.succAbove_zero] at h2
  rw [mul_comm (x 0), ← h2, mul_comm]

/-- If the rows `1, …, N` of `P` are lower triangular and a vector `x` with first coordinate
`∏ (X - P_(i+1,i+1))` satisfies `(X - P) x = p e_0`, then the characteristic polynomial of `P`
is `p`. -/
theorem charpoly_eq_of_mulVec {N : ℕ} (P : Matrix (Fin (N + 1)) (Fin (N + 1)) R)
    (hlow : ∀ i j : Fin N, i < j → P i.succ j.succ = 0) (x : Fin (N + 1) → R[X]) (p : R[X])
    (hx0 : x 0 = ∏ i : Fin N, (X - C (P i.succ i.succ)))
    (hx : charmatrix P *ᵥ x = Pi.single 0 p) : P.charpoly = p := by
  have h := mul_det_eq_of_mulVec _ x p hx
  have hsub : ((charmatrix P).submatrix Fin.succ Fin.succ).det = x 0 := by
    rw [hx0, det_of_isLowerTriangular]
    · simp
    · intro i j hij
      have hij' : i < j := OrderDual.toDual_lt_toDual.mp hij
      have hne : i.succ ≠ j.succ := (Fin.succ_injective _).ne (ne_of_lt hij')
      simp [charmatrix_apply_ne P _ _ hne, hlow i j hij']
  rw [hsub] at h
  have hmon : (x 0).Monic := by
    rw [hx0]
    exact monic_prod_of_monic _ _ fun i _ => monic_X_sub_C (P i.succ i.succ)
  rw [Matrix.charpoly]
  exact hmon.isRegular.left (show x 0 * _ = x 0 * _ by rw [h, mul_comm])


/-! ### Evaluating the actions -/

theorem pprodAct_self (a k : ℕ) (c f : ℕ → R) :
    pprodAct a k c f a = (∑ i ∈ Finset.range k, -c (a + i) * f (a + i)) + f (a + k) := by
  simp [pprodAct]

theorem pprodAct_of_lt {a k b : ℕ} (h : b < a) (c f : ℕ → R) : pprodAct a k c f b = f b := by
  simp only [pprodAct]
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]

theorem pprodAct_of_gt {a k b : ℕ} (h : a + k < b) (c f : ℕ → R) : pprodAct a k c f b = f b := by
  simp only [pprodAct]
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]

theorem pprodAct_of_mid {a k b : ℕ} (h1 : a < b) (h2 : b ≤ a + k) (c f : ℕ → R) :
    pprodAct a k c f b = -f (b - 1) := by
  simp only [pprodAct]
  rw [ite_eq_right (by omega), ite_eq_left ⟨h1, h2⟩]

theorem coreAct_of_lt {j b : ℕ} (h : b < j) (β : ℕ → ℕ → R) (f : ℕ → R) :
    coreAct j β f b = f b := by
  simp only [coreAct]
  rw [ite_eq_right (by omega)]

theorem coreAct_of_ge {j b : ℕ} (h : j + 3 ≤ b) (β : ℕ → ℕ → R) (f : ℕ → R) :
    coreAct j β f b = f b := by
  simp only [coreAct]
  rw [ite_eq_right (by omega)]

theorem coreAct_add {j r : ℕ} (h : r < 3) (β : ℕ → ℕ → R) (f : ℕ → R) :
    coreAct j β f (j + r) = β r 0 * f j + β r 1 * f (j + 1) + β r 2 * f (j + 2) := by
  simp only [coreAct]
  rw [ite_eq_left (by omega), Nat.add_sub_cancel_left]

/-- The action of `pprod 0 k * core k β * pprod (k + 2) k` on families indexed by `ℕ`. -/
def pathAct (k : ℕ) (c : ℕ → R) (β : ℕ → ℕ → R) (f : ℕ → R) : ℕ → R :=
  pprodAct 0 k c (coreAct k β (pprodAct (k + 2) k c f))

theorem pathAct_zero (k : ℕ) (c : ℕ → R) (β : ℕ → ℕ → R) (f : ℕ → R) :
    pathAct k c β f 0 = (∑ i ∈ Finset.range k, -c i * f i) + β 0 0 * f k +
      β 0 1 * f (k + 1) +
      β 0 2 * ((∑ i ∈ Finset.range k, -c (k + 2 + i) * f (k + 2 + i)) + f (2 * k + 2)) := by
  unfold pathAct
  rw [pprodAct_self]
  simp only [zero_add]
  have hs : ∀ i ∈ Finset.range k,
      -c i * coreAct k β (pprodAct (k + 2) k c f) i = -c i * f i := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [coreAct_of_lt hi, pprodAct_of_lt (by omega)]
  rw [Finset.sum_congr rfl hs]
  have hk := coreAct_add (j := k) (r := 0) (by omega) β (pprodAct (k + 2) k c f)
  rw [add_zero] at hk
  rw [hk, pprodAct_of_lt (by omega), pprodAct_of_lt (by omega), pprodAct_self,
    show k + 2 + k = 2 * k + 2 by omega]
  ring

theorem pathAct_low {k b : ℕ} (h1 : 0 < b) (h2 : b ≤ k) (c : ℕ → R) (β : ℕ → ℕ → R)
    (f : ℕ → R) : pathAct k c β f b = -f (b - 1) := by
  unfold pathAct
  rw [pprodAct_of_mid h1 (by omega), coreAct_of_lt (by omega), pprodAct_of_lt (by omega)]

theorem pathAct_mid₁ (k : ℕ) (c : ℕ → R) (β : ℕ → ℕ → R) (h12 : β 1 2 = 0) (f : ℕ → R) :
    pathAct k c β f (k + 1) = β 1 0 * f k + β 1 1 * f (k + 1) := by
  unfold pathAct
  rw [pprodAct_of_gt (by omega), coreAct_add (by omega), pprodAct_of_lt (by omega),
    pprodAct_of_lt (by omega), h12]
  ring

theorem pathAct_mid₂ (k : ℕ) (c : ℕ → R) (β : ℕ → ℕ → R) (h22 : β 2 2 = 0) (f : ℕ → R) :
    pathAct k c β f (k + 2) = β 2 0 * f k + β 2 1 * f (k + 1) := by
  unfold pathAct
  rw [pprodAct_of_gt (by omega), coreAct_add (by omega), pprodAct_of_lt (by omega),
    pprodAct_of_lt (by omega), h22]
  ring

theorem pathAct_high {k b : ℕ} (h1 : k + 2 < b) (h2 : b ≤ 2 * k + 2) (c : ℕ → R)
    (β : ℕ → ℕ → R) (f : ℕ → R) : pathAct k c β f b = -f (b - 1) := by
  unfold pathAct
  rw [pprodAct_of_gt (by omega), coreAct_of_ge (by omega), pprodAct_of_mid h1 (by omega)]

/-! ### The path matrix with a `3 × 3` core -/

/-- The product `pprod 0 k * core k β * pprod (k + 2) k` on `2 k + 3` lines. -/
def pathMat (k : ℕ) (c : ℕ → R) (β : ℕ → ℕ → R) : Matrix (Fin (2 * k + 3)) (Fin (2 * k + 3)) R :=
  pprod (2 * k + 3) 0 k c * core (2 * k + 3) k β * pprod (2 * k + 3) (k + 2) k c

theorem vget_pathMat_mulVec (k : ℕ) (c : ℕ → R) (β : ℕ → ℕ → R) (v : Fin (2 * k + 3) → R) :
    vget (pathMat k c β *ᵥ v) = pathAct k c β (vget v) := by
  rw [pathMat, ← mulVec_mulVec, ← mulVec_mulVec, vget_pprod_mulVec (by omega),
    vget_core_mulVec (by omega), vget_pprod_mulVec (by omega)]
  rfl

theorem pathMat_apply (k : ℕ) (c : ℕ → R) (β : ℕ → ℕ → R) (a b : Fin (2 * k + 3)) :
    pathMat k c β a b = pathAct k c β (fun i => if i = (b : ℕ) then 1 else 0) a := by
  have h := congrFun (vget_pathMat_mulVec k c β (Pi.single b 1)) a
  rw [vget_fin, mulVec_single_one, col_apply] at h
  rw [h]
  congr 1
  funext i
  exact vget_single b i

theorem pathMat_map {S : Type*} [CommRing S] (φ : R →+* S) (k : ℕ) (c : ℕ → R)
    (β : ℕ → ℕ → R) :
    (pathMat k c β).map φ = pathMat k (fun i => φ (c i)) (fun a b => φ (β a b)) := by
  rw [pathMat, pathMat, Matrix.map_mul, Matrix.map_mul, pprod_map, pprod_map, core_map]

theorem pathMat_succ_succ_of_lt (k : ℕ) (c : ℕ → R) (β : ℕ → ℕ → R) (h12 : β 1 2 = 0)
    (h22 : β 2 2 = 0) (i j : Fin (2 * k + 2)) (hij : i < j) :
    pathMat k c β i.succ j.succ = 0 := by
  rw [pathMat_apply]
  have hij' : (i : ℕ) < j := hij
  have hj := j.2
  simp only [Fin.val_succ]
  by_cases h1 : (i : ℕ) + 1 ≤ k
  · rw [pathAct_low (by omega) h1]
    simp only [neg_eq_zero, ite_eq_right_iff]
    omega
  by_cases h2 : (i : ℕ) = k
  · rw [h2, pathAct_mid₁ k c β h12]
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    ring
  by_cases h3 : (i : ℕ) = k + 1
  · rw [h3, pathAct_mid₂ k c β h22]
    rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    ring
  · rw [pathAct_high (by omega) (by omega)]
    simp only [neg_eq_zero, ite_eq_right_iff]
    omega

theorem pathMat_succ_succ_self (k : ℕ) (c : ℕ → R) (β : ℕ → ℕ → R) (h12 : β 1 2 = 0)
    (h22 : β 2 2 = 0) (i : Fin (2 * k + 2)) :
    pathMat k c β i.succ i.succ = if (i : ℕ) = k then β 1 1 else 0 := by
  rw [pathMat_apply]
  have hi := i.2
  generalize hb : (i.succ : ℕ) = b
  have hb' : (i : ℕ) + 1 = b := by rw [← hb, Fin.val_succ]
  by_cases h1 : b ≤ k
  · rw [pathAct_low (by omega) h1, ite_eq_right (by omega), ite_eq_right (by omega)]
    simp
  by_cases h2 : (i : ℕ) = k
  · obtain rfl : b = k + 1 := by omega
    rw [pathAct_mid₁ k c β h12, ite_eq_left h2]
    simp
  by_cases h3 : (i : ℕ) = k + 1
  · obtain rfl : b = k + 2 := by omega
    rw [pathAct_mid₂ k c β h22, ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega)]
    ring
  · rw [pathAct_high (by omega) (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
    simp

theorem prod_X_sub_C_pathMat_diag (k : ℕ) (c : ℕ → R) (β : ℕ → ℕ → R) (h12 : β 1 2 = 0)
    (h22 : β 2 2 = 0) :
    ∏ i : Fin (2 * k + 2), (X - C (pathMat k c β i.succ i.succ)) =
      X ^ (2 * k + 1) * (X - C (β 1 1)) := by
  simp only [pathMat_succ_succ_self k c β h12 h22]
  rw [Fin.prod_univ_eq_prod_range (fun i => X - C (if i = k then β 1 1 else 0)) (2 * k + 2)]
  have hk : k ∈ Finset.range (2 * k + 2) := Finset.mem_range.2 (by omega)
  rw [← Finset.mul_prod_erase _ _ hk, ite_eq_left rfl]
  rw [Finset.prod_congr rfl (g := fun _ => (X : R[X])) (fun i hi => by
    rw [ite_eq_right (Finset.ne_of_mem_erase hi), map_zero, sub_zero])]
  rw [Finset.prod_const, Finset.card_erase_of_mem hk, Finset.card_range,
    show 2 * k + 2 - 1 = 2 * k + 1 by omega]
  ring

theorem charmatrix_mulVec_apply {m : Type*} [Fintype m] [DecidableEq m] (M : Matrix m m R)
    (x : m → R[X]) (a : m) : (charmatrix M *ᵥ x) a = X * x a - (M.map C *ᵥ x) a := by
  rw [charmatrix, sub_mulVec, Pi.sub_apply, scalar_apply, mulVec_diagonal,
    RingHom.mapMatrix_apply]

/-- The vector solving `(X - P) x = p e_0` for `P = pathMat k c β`. -/
def pathVec (k : ℕ) (β : ℕ → ℕ → R) : ℕ → R[X] := fun i =>
  if i ≤ k then (-1) ^ i * X ^ (2 * k + 1 - i) * (X - C (β 1 1))
  else if i = k + 1 then (-1) ^ k * C (β 1 0) * X ^ (k + 1)
  else if i ≤ 2 * k + 2 then
    (-1) ^ i * X ^ (2 * k + 2 - i) * (C (β 2 0) * (X - C (β 1 1)) + C (β 1 0) * C (β 2 1))
  else 0

theorem pathVec_low (k : ℕ) (β : ℕ → ℕ → R) {i : ℕ} (h : i ≤ k) :
    pathVec k β i = (-1) ^ i * X ^ (2 * k + 1 - i) * (X - C (β 1 1)) := by
  rw [pathVec, ite_eq_left h]

theorem pathVec_mid (k : ℕ) (β : ℕ → ℕ → R) :
    pathVec k β (k + 1) = (-1) ^ k * C (β 1 0) * X ^ (k + 1) := by
  rw [pathVec, ite_eq_right (by omega), ite_eq_left rfl]

theorem pathVec_high (k : ℕ) (β : ℕ → ℕ → R) {i : ℕ} (h1 : k + 2 ≤ i) (h2 : i ≤ 2 * k + 2) :
    pathVec k β i = (-1) ^ i * X ^ (2 * k + 2 - i) *
      (C (β 2 0) * (X - C (β 1 1)) + C (β 1 0) * C (β 2 1)) := by
  rw [pathVec, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left h2]

theorem pathVec_top (k : ℕ) (β : ℕ → ℕ → R) {i : ℕ} (h : 2 * k + 2 < i) : pathVec k β i = 0 := by
  rw [pathVec, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

theorem vget_pathVec (k : ℕ) (β : ℕ → ℕ → R) :
    vget (fun a : Fin (2 * k + 3) => pathVec k β a) = pathVec k β := by
  funext b
  by_cases hb : b < 2 * k + 3
  · rw [vget_of_lt _ hb]
  · rw [vget_of_le _ (by omega), pathVec_top k β (by omega)]

/-- **Characteristic polynomial of a path product with a `3 × 3` core.** On `2 k + 3` lines,
let `P = pprod 0 k c * core k β * pprod (k + 2) k c`, with `β 1 2 = β 2 2 = 0`. Writing
`Y = X - β₁₁` and `W = β₂₀ Y + β₁₀ β₂₁`, the characteristic polynomial of `P` is
`Y (X^(2k+2) + Σ_{i<k} (-1)^i c_i X^(2k+1-i) + (-1)^(k+1) β₀₀ X^(k+1))
 + (-1)^(k+1) β₀₁ β₁₀ X^(k+1) + β₀₂ W (Σ_{i<k} (-1)^(k+i) c_(k+2+i) X^(k-i) - 1)`. -/
theorem charpoly_pathMat (k : ℕ) (c : ℕ → R) (β : ℕ → ℕ → R) (h12 : β 1 2 = 0)
    (h22 : β 2 2 = 0) :
    (pathMat k c β).charpoly =
      (X - C (β 1 1)) * (X ^ (2 * k + 2) +
          (∑ i ∈ Finset.range k, (-1) ^ i * C (c i) * X ^ (2 * k + 1 - i)) +
          (-1) ^ (k + 1) * C (β 0 0) * X ^ (k + 1)) +
        (-1) ^ (k + 1) * C (β 0 1) * C (β 1 0) * X ^ (k + 1) +
        C (β 0 2) * (C (β 2 0) * (X - C (β 1 1)) + C (β 1 0) * C (β 2 1)) *
          ((∑ i ∈ Finset.range k, (-1) ^ (k + i) * C (c (k + 2 + i)) * X ^ (k - i)) - 1) := by
  apply charpoly_eq_of_mulVec (N := 2 * k + 2) _
    (fun i j hij => pathMat_succ_succ_of_lt k c β h12 h22 i j hij)
    (fun a => pathVec k β a)
  · rw [prod_X_sub_C_pathMat_diag k c β h12 h22]
    change pathVec k β 0 = _
    rw [pathVec_low k β (Nat.zero_le _), Nat.sub_zero]
    ring
  · have hC12 : (fun a b => C (β a b)) 1 2 = (0 : R[X]) := by simp [h12]
    have hC22 : (fun a b => C (β a b)) 2 2 = (0 : R[X]) := by simp [h22]
    funext a
    have hv := congrFun (vget_pathMat_mulVec k (fun i => C (c i)) (fun a b => C (β a b))
      (fun a : Fin (2 * k + 3) => pathVec k β a)) a
    rw [vget_fin, vget_pathVec, ← pathMat_map] at hv
    rw [charmatrix_mulVec_apply, hv]
    change X * pathVec k β a - _ = _
    have ha := a.2
    by_cases h0 : (a : ℕ) = 0
    · have ha0 : a = 0 := Fin.ext h0
      rw [ha0, Pi.single_eq_same]
      simp only [Fin.val_zero, pathAct_zero]
      have s1 : (∑ i ∈ Finset.range k, -(fun i => C (c i)) i * pathVec k β i) =
          -((∑ i ∈ Finset.range k, (-1) ^ i * C (c i) * X ^ (2 * k + 1 - i)) *
            (X - C (β 1 1))) := by
        rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [Finset.mem_range] at hi
        rw [pathVec_low k β (by omega)]
        ring
      have s2 : (∑ i ∈ Finset.range k,
            -(fun i => C (c i)) (k + 2 + i) * pathVec k β (k + 2 + i)) =
          -((∑ i ∈ Finset.range k, (-1) ^ (k + i) * C (c (k + 2 + i)) * X ^ (k - i)) *
            (C (β 2 0) * (X - C (β 1 1)) + C (β 1 0) * C (β 2 1))) := by
        rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [Finset.mem_range] at hi
        rw [pathVec_high k β (by omega) (by omega), show 2 * k + 2 - (k + 2 + i) = k - i by omega]
        ring
      rw [s1, s2, pathVec_low k β le_rfl, pathVec_low k β (Nat.zero_le _), pathVec_mid,
        pathVec_high k β (by omega) le_rfl, show 2 * k + 1 - k = k + 1 by omega,
        show 2 * k + 1 - 0 = 2 * k + 1 by omega, Nat.sub_self,
        (Even.neg_one_pow ⟨k + 1, by ring⟩ : (-1 : R[X]) ^ (2 * k + 2) = 1)]
      ring
    · rw [Pi.single_eq_of_ne (fun h => h0 (by rw [h]; rfl))]
      by_cases h1 : (a : ℕ) ≤ k
      · rw [pathAct_low (by omega) h1]
        obtain ⟨j, hj⟩ : ∃ j, (a : ℕ) = j + 1 := ⟨(a : ℕ) - 1, by omega⟩
        rw [hj, Nat.add_sub_cancel, pathVec_low k β (by omega), pathVec_low k β (by omega),
          show 2 * k + 1 - j = (2 * k + 1 - (j + 1)) + 1 by omega]
        ring
      by_cases h2 : (a : ℕ) = k + 1
      · rw [h2, pathAct_mid₁ k _ _ hC12, pathVec_mid, pathVec_low k β le_rfl,
          show 2 * k + 1 - k = k + 1 by omega]
        ring
      by_cases h3 : (a : ℕ) = k + 2
      · rw [h3, pathAct_mid₂ k _ _ hC22, pathVec_high k β le_rfl (by omega), pathVec_mid,
          pathVec_low k β le_rfl, show 2 * k + 1 - k = k + 1 by omega,
          show 2 * k + 2 - (k + 2) = k by omega]
        ring
      · rw [pathAct_high (by omega) (by omega)]
        obtain ⟨j, hj⟩ : ∃ j, (a : ℕ) = j + 1 := ⟨(a : ℕ) - 1, by omega⟩
        rw [hj, Nat.add_sub_cancel, pathVec_high k β (by omega) (by omega),
          pathVec_high k β (by omega) (by omega),
          show 2 * k + 2 - j = (2 * k + 2 - (j + 1)) + 1 by omega]
        ring

/-! ### Commutation of factors on separated lines -/

theorem commute_of_act {A B : Matrix (Fin n) (Fin n) R} (FA FB : (ℕ → R) → ℕ → R)
    (hA : ∀ v, vget (A *ᵥ v) = FA (vget v)) (hB : ∀ v, vget (B *ᵥ v) = FB (vget v))
    (h : ∀ f, FA (FB f) = FB (FA f)) : Commute A B := by
  rw [Commute, SemiconjBy, ext_iff_mulVec]
  intro v
  apply vget_injective
  simp only [← mulVec_mulVec, hA, hB]
  exact h _

theorem sfac_commute_sfac {i j : ℕ} (hij : i + 2 ≤ j) (hj : j + 1 < n) (c d : R) :
    Commute (sfac n i c) (sfac n j d) := by
  refine commute_of_act (sfacAct i c) (sfacAct j d) (vget_sfac_mulVec (by omega) c)
    (vget_sfac_mulVec hj d) fun f => ?_
  funext b
  simp only [sfacAct]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem sfac_commute_core {i j : ℕ} (hij : i + 2 ≤ j) (hj : j + 3 ≤ n) (c : R)
    (β : ℕ → ℕ → R) : Commute (sfac n i c) (core n j β) := by
  refine commute_of_act (sfacAct i c) (coreAct j β) (vget_sfac_mulVec (by omega) c)
    (vget_core_mulVec hj β) fun f => ?_
  funext b
  simp only [sfacAct, coreAct]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem core_commute_sfac {i j : ℕ} (hji : j + 3 ≤ i) (hi : i + 1 < n) (c : R)
    (β : ℕ → ℕ → R) : Commute (core n j β) (sfac n i c) := by
  refine commute_of_act (coreAct j β) (sfacAct i c) (vget_core_mulVec (by omega) β)
    (vget_sfac_mulVec hi c) fun f => ?_
  funext b
  simp only [sfacAct, coreAct]
  split_ifs <;> first | rfl | (exfalso; omega)

/-! ### Independence of the order of the factors -/

theorem charpoly_prod_perm_mul {m : Type*} [Fintype m] [DecidableEq m]
    (y : ℕ → Matrix m m R) (hy : ∀ i j, i + 2 ≤ j → Commute (y i) (y j)) (N : ℕ) :
    ∀ l : List ℕ, l.Perm (List.range N) → ∀ Z : Matrix m m R,
      (∀ i, i + 2 ≤ N → Commute (y i) Z) →
      ((l.map y).prod * Z).charpoly = (((List.range N).map y).prod * Z).charpoly := by
  induction N with
  | zero =>
    intro l hl Z _
    rw [List.range_zero, List.perm_nil] at hl
    subst hl
    rfl
  | succ N ih =>
    intro l hl Z hZ
    have hmem : N ∈ l := hl.symm.subset (List.mem_range.2 (Nat.lt_succ_self N))
    obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hmem
    have hperm : (l₂ ++ l₁).Perm (List.range N) := by
      have h1 : (l₁ ++ N :: l₂).Perm (N :: (l₂ ++ l₁)) :=
        List.perm_middle.trans (List.Perm.cons N List.perm_append_comm)
      have h2 : (List.range (N + 1)).Perm (N :: List.range N) := by
        rw [List.range_succ]
        exact List.perm_append_singleton _ _
      exact List.Perm.cons_inv (h1.symm.trans (hl.trans h2))
    have hlt : ∀ i ∈ l₂ ++ l₁, i < N := fun i hi => List.mem_range.1 (hperm.subset hi)
    have hc₂ : Commute (l₂.map y).prod Z := by
      apply Commute.list_prod_left
      intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
      exact hZ i (by have := hlt i (List.mem_append_left _ hi); omega)
    have hZ' : ∀ i, i + 2 ≤ N → Commute (y i) (y N * Z) :=
      fun i hi => (hy i N hi).mul_right (hZ i (by omega))
    calc ((List.map y (l₁ ++ N :: l₂)).prod * Z).charpoly
        = ((l₁.map y).prod * (y N * Z * (l₂.map y).prod)).charpoly := by
          rw [List.map_append, List.prod_append, List.map_cons, List.prod_cons, mul_assoc,
            mul_assoc, hc₂.eq, mul_assoc]
      _ = ((y N * Z) * ((l₂.map y).prod * (l₁.map y).prod)).charpoly := by
          rw [charpoly_mul_comm, mul_assoc]
      _ = (((l₂ ++ l₁).map y).prod * (y N * Z)).charpoly := by
          rw [charpoly_mul_comm, List.map_append, List.prod_append]
      _ = (((List.range N).map y).prod * (y N * Z)).charpoly := ih _ hperm _ hZ'
      _ = (((List.range (N + 1)).map y).prod * Z).charpoly := by
          rw [List.range_succ, List.map_append, List.prod_append, List.map_singleton,
            List.prod_singleton, mul_assoc]

/-- **Order independence.** If `y i` and `y j` commute whenever `i + 2 ≤ j`, then the product
of the `y i` over any ordering of `0, …, N - 1` has the same characteristic polynomial as the
product in increasing order. -/
theorem charpoly_prod_perm {m : Type*} [Fintype m] [DecidableEq m]
    (y : ℕ → Matrix m m R) (hy : ∀ i j, i + 2 ≤ j → Commute (y i) (y j)) {N : ℕ}
    {l : List ℕ} (hl : l.Perm (List.range N)) :
    (l.map y).prod.charpoly = ((List.range N).map y).prod.charpoly := by
  have h := charpoly_prod_perm_mul y hy N l hl 1 (fun i _ => Commute.one_right _)
  rwa [mul_one, mul_one] at h

/-! ### Specializations -/

theorem pprod_add (a k₁ k₂ : ℕ) (c : ℕ → R) :
    pprod n a (k₁ + k₂) c = pprod n a k₁ c * pprod n (a + k₁) k₂ c := by
  rw [pprod, pprod, pprod, List.range_add, List.map_append, List.prod_append, List.map_map]
  congr 3
  funext i
  simp [Function.comp, Nat.add_assoc]

/-- The `3 × 3` block of two consecutive simple factors with scalars `σ` and `τ`:
rows `(-σ, -τ, 1)`, `(-1, 0, 0)` and `(0, -1, 0)`. -/
def ordCore (σ τ : R) : ℕ → ℕ → R := fun a b =>
  if a = 0 then (if b = 0 then -σ else if b = 1 then -τ else if b = 2 then 1 else 0)
  else if a = 1 then (if b = 0 then -1 else 0)
  else if a = 2 then (if b = 1 then -1 else 0) else 0

theorem core_ordCore {j : ℕ} (h : j + 3 ≤ n) (σ τ : R) :
    core n j (ordCore σ τ) = sfac n j σ * sfac n (j + 1) τ := by
  rw [ext_iff_mulVec]
  intro v
  apply vget_injective
  rw [vget_core_mulVec h, ← mulVec_mulVec, vget_sfac_mulVec (by omega),
    vget_sfac_mulVec (by omega)]
  funext b
  simp only [coreAct, sfacAct, ordCore]
  by_cases h0 : b = j
  · subst h0
    simp only [le_refl, true_and, ite_true, Nat.sub_self]
    rw [ite_eq_left (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega)]
    rw [ite_eq_right (by omega), ite_eq_right (by omega), show b + 1 + 1 = b + 2 by omega]
    ring
  by_cases h1 : b = j + 1
  · subst h1
    simp
    omega
  by_cases h2 : b = j + 2
  · subst h2; simp
  · rw [ite_eq_right (by omega), ite_eq_right h0, ite_eq_right h1,
      ite_eq_right (by omega), ite_eq_right (by omega)]

theorem pathMat_ordCore (k : ℕ) (c : ℕ → R) :
    pathMat k c (ordCore (c k) (c (k + 1))) = pprod (2 * k + 3) 0 (2 * k + 2) c := by
  rw [pathMat, core_ordCore (by omega), show 2 * k + 2 = k + (2 + k) by omega, pprod_add,
    pprod_add, pprod_succ, pprod_succ, pprod_zero]
  simp only [zero_add, one_mul, mul_assoc]
  rw [show k + 0 = k by omega]

theorem sum_range_two_mul_add_two {M : Type*} [AddCommMonoid M] (k : ℕ) (f : ℕ → M) :
    ∑ j ∈ Finset.range (2 * k + 2), f j =
      (∑ j ∈ Finset.range k, f j) + f k + f (k + 1) + ∑ i ∈ Finset.range k, f (k + 2 + i) := by
  rw [show 2 * k + 2 = k + 2 + k by omega, Finset.sum_range_add, Finset.sum_range_add,
    Finset.sum_range_succ, Finset.sum_range_one]
  simp only [add_zero, add_assoc]

/-- **Characteristic polynomial of a full path product.** The product of the `2 k + 2` simple
factors on `2 k + 3` lines, in increasing order, has characteristic polynomial
`X^(2k+3) + Σ_{j<2k+2} (-1)^j c_j X^(2k+2-j) - 1`. -/
theorem charpoly_pprod (k : ℕ) (c : ℕ → R) :
    (pprod (2 * k + 3) 0 (2 * k + 2) c).charpoly =
      X ^ (2 * k + 3) + (∑ j ∈ Finset.range (2 * k + 2), (-1) ^ j * C (c j) * X ^ (2 * k + 2 - j))
        - 1 := by
  rw [← pathMat_ordCore, charpoly_pathMat k c _ (by simp [ordCore]) (by simp [ordCore])]
  have e00 : ordCore (c k) (c (k + 1)) 0 0 = -c k := by simp [ordCore]
  have e01 : ordCore (c k) (c (k + 1)) 0 1 = -c (k + 1) := by simp [ordCore]
  have e02 : ordCore (c k) (c (k + 1)) 0 2 = 1 := by simp [ordCore]
  have e10 : ordCore (c k) (c (k + 1)) 1 0 = -1 := by simp [ordCore]
  have e11 : ordCore (c k) (c (k + 1)) 1 1 = 0 := by simp [ordCore]
  have e20 : ordCore (c k) (c (k + 1)) 2 0 = 0 := by simp [ordCore]
  have e21 : ordCore (c k) (c (k + 1)) 2 1 = -1 := by simp [ordCore]
  rw [e00, e01, e02, e10, e11, e20, e21, sum_range_two_mul_add_two]
  have s1 : ∀ i ∈ Finset.range k, (-1) ^ i * C (c i) * X ^ (2 * k + 2 - i) =
      X * ((-1) ^ i * C (c i) * X ^ (2 * k + 1 - i)) := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [show 2 * k + 2 - i = (2 * k + 1 - i) + 1 by omega]
    ring
  have s2 : ∀ i ∈ Finset.range k, (-1) ^ (k + 2 + i) * C (c (k + 2 + i)) *
      X ^ (2 * k + 2 - (k + 2 + i)) = (-1) ^ (k + i) * C (c (k + 2 + i)) * X ^ (k - i) := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [show 2 * k + 2 - (k + 2 + i) = k - i by omega]
    ring
  rw [Finset.sum_congr rfl s1, ← Finset.mul_sum, Finset.sum_congr rfl s2,
    show 2 * k + 2 - k = k + 2 by omega, show 2 * k + 2 - (k + 1) = k + 1 by omega]
  simp only [map_neg, map_one, map_zero, sub_zero]
  ring

/-- **Characteristic polynomial of a path product with a pattern block.** If moreover
`β₁₁ = 1`, `β₂₁ = 0` and `β₀₂ β₂₀ = -1`, then the characteristic polynomial of
`pathMat k c β` is `(X - 1) Q + (-1)^(k+1) β₀₁ β₁₀ X^(k+1)` with
`Q = X^(2k+2) + Σ_{i<k} (-1)^i c_i X^(2k+1-i) + (-1)^(k+1) β₀₀ X^(k+1)
 + Σ_{i<k} (-1)^(k+1+i) c_(k+2+i) X^(k-i) + 1`. -/
theorem charpoly_pathMat_pattern (k : ℕ) (c : ℕ → R) (β : ℕ → ℕ → R) (h12 : β 1 2 = 0)
    (h22 : β 2 2 = 0) (h11 : β 1 1 = 1) (h21 : β 2 1 = 0) (h0220 : β 0 2 * β 2 0 = -1) :
    (pathMat k c β).charpoly =
      (X - 1) * (X ^ (2 * k + 2) +
          (∑ i ∈ Finset.range k, (-1) ^ i * C (c i) * X ^ (2 * k + 1 - i)) +
          (-1) ^ (k + 1) * C (β 0 0) * X ^ (k + 1) +
          (∑ i ∈ Finset.range k, (-1) ^ (k + 1 + i) * C (c (k + 2 + i)) * X ^ (k - i)) + 1) +
        (-1) ^ (k + 1) * C (β 0 1) * C (β 1 0) * X ^ (k + 1) := by
  rw [charpoly_pathMat k c β h12 h22, h11, h21, map_one, map_zero, mul_zero, add_zero]
  have hC : C (β 0 2) * C (β 2 0) = (-1 : R[X]) := by rw [← map_mul, h0220, map_neg, map_one]
  have s : ∀ i ∈ Finset.range k, (-1) ^ (k + 1 + i) * C (c (k + 2 + i)) * X ^ (k - i) =
      -((-1) ^ (k + i) * C (c (k + 2 + i)) * X ^ (k - i)) := by
    intro i _
    ring
  rw [Finset.sum_congr rfl s, Finset.sum_neg_distrib]
  generalize (∑ i ∈ Finset.range k, (-1) ^ (k + i) * C (c (k + 2 + i)) * X ^ (k - i)) = S
  linear_combination (X - 1) * (S - 1) * hC

end Langlands.LinearAlgebra.PathCoxeter
