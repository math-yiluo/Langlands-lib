import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Data.Matrix.Basis

/-! # Two minors of products of chain factors -/

namespace Langlands.LinearAlgebra.ChainCoxeter

open Matrix

variable {R : Type*} [CommRing R]

/-- A chain factor at the edge `j` of the chain with vertices `Fin (r + 1)`: it fixes every basis
vector other than `e_j` and `e_{j+1}`, sends `e_{j+1}` to `a • e_j`, and sends `e_j` into the
span of `e_j` and `e_{j+1}` with coefficient `b` on `e_{j+1}`. -/
structure IsChainFactor {r : ℕ} (g : Matrix (Fin (r + 1)) (Fin (r + 1)) R) (j : Fin r)
    (a b : R) : Prop where
  apply_of_ne : ∀ i c, c ≠ j.castSucc → c ≠ j.succ → g i c = (1 : Matrix _ _ R) i c
  apply_succ : ∀ i, g i j.succ = if i = j.castSucc then a else 0
  apply_succ_castSucc : g j.succ j.castSucc = b
  apply_castSucc_of_ne : ∀ i, i ≠ j.castSucc → i ≠ j.succ → g i j.castSucc = 0

/-- A list of factors in which every edge occurs exactly once, by a chain factor, and every other
factor is the identity. -/
structure IsChainList {ι : Type*} {r : ℕ} (l : List ι)
    (F : ι → Matrix (Fin (r + 1)) (Fin (r + 1)) R) (E : ι → Option (Fin r))
    (a b : Fin r → R) : Prop where
  eq_one : ∀ i ∈ l, E i = none → F i = 1
  isChainFactor : ∀ i ∈ l, ∀ j, E i = some j → IsChainFactor (F i) j (a j) (b j)
  countP_eq_one : ∀ j, l.countP (fun i => E i = some j) = 1

section Vertex

variable {n : ℕ}

/-- `X` fixes the basis vector `e_p` and preserves the span of the others. -/
def FixesVertex (X : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (p : Fin (n + 1)) : Prop :=
  X p p = 1 ∧ (∀ i, X (p.succAbove i) p = 0) ∧ ∀ j, X p (p.succAbove j) = 0

theorem fixesVertex_one (p : Fin (n + 1)) : FixesVertex (1 : Matrix (Fin (n + 1)) _ R) p :=
  ⟨one_apply_eq p, fun i => one_apply_ne (Fin.succAbove_ne p i),
    fun j => one_apply_ne (Fin.succAbove_ne p j).symm⟩

theorem FixesVertex.mul {X Y : Matrix (Fin (n + 1)) (Fin (n + 1)) R} {p : Fin (n + 1)}
    (hX : FixesVertex X p) (hY : FixesVertex Y p) : FixesVertex (X * Y) p := by
  refine ⟨?_, fun i => ?_, fun j => ?_⟩
  · rw [mul_apply, Fin.sum_univ_succAbove _ p, hX.1, hY.1, one_mul]
    simp [hX.2.2, hY.2.1]
  · rw [mul_apply, Fin.sum_univ_succAbove _ p]
    simp [hX.2.1, hY.2.1]
  · rw [mul_apply, Fin.sum_univ_succAbove _ p]
    simp [hX.2.2, hY.2.2]

theorem fixesVertex_prod (L : List (Matrix (Fin (n + 1)) (Fin (n + 1)) R)) {p : Fin (n + 1)}
    (h : ∀ X ∈ L, FixesVertex X p) : FixesVertex L.prod p := by
  induction L with
  | nil => exact fixesVertex_one p
  | cons X L ih =>
    rw [List.prod_cons]
    exact (h X List.mem_cons_self).mul (ih fun Y hY => h Y (List.mem_cons_of_mem X hY))

theorem submatrix_mul_of_col (X Y : Matrix (Fin (n + 1)) (Fin (n + 1)) R) {p : Fin (n + 1)}
    (h : ∀ i, X (p.succAbove i) p = 0) :
    (X * Y).submatrix p.succAbove p.succAbove =
      X.submatrix p.succAbove p.succAbove * Y.submatrix p.succAbove p.succAbove := by
  ext i j
  simp only [submatrix_apply, mul_apply]
  rw [Fin.sum_univ_succAbove _ p, h, zero_mul, zero_add]

theorem submatrix_mul_of_row (X Y : Matrix (Fin (n + 1)) (Fin (n + 1)) R) {p : Fin (n + 1)}
    (h : ∀ j, Y p (p.succAbove j) = 0) :
    (X * Y).submatrix p.succAbove p.succAbove =
      X.submatrix p.succAbove p.succAbove * Y.submatrix p.succAbove p.succAbove := by
  ext i j
  simp only [submatrix_apply, mul_apply]
  rw [Fin.sum_univ_succAbove _ p, h, mul_zero, zero_add]

theorem submatrix_prod (L : List (Matrix (Fin (n + 1)) (Fin (n + 1)) R)) {p : Fin (n + 1)}
    (h : ∀ X ∈ L, FixesVertex X p) :
    L.prod.submatrix p.succAbove p.succAbove =
      (L.map fun X => X.submatrix p.succAbove p.succAbove).prod := by
  induction L with
  | nil => exact submatrix_one _ (Fin.succAbove_right_injective (p := p))
  | cons X L ih =>
    rw [List.prod_cons, submatrix_mul_of_col _ _ (h X List.mem_cons_self).2.1,
      ih fun Y hY => h Y (List.mem_cons_of_mem X hY), List.map_cons, List.prod_cons]

theorem FixesVertex.det_eq {X : Matrix (Fin (n + 1)) (Fin (n + 1)) R} {p : Fin (n + 1)}
    (h : FixesVertex X p) : X.det = (X.submatrix p.succAbove p.succAbove).det := by
  rw [det_succ_column X p, Finset.sum_eq_single p]
  · rw [h.1, mul_one, show ((p : ℕ) + p) = 2 * p by ring, pow_mul, neg_one_sq, one_pow, one_mul]
  · intro i _ hi
    obtain ⟨i', rfl⟩ := Fin.exists_succAbove_eq hi
    rw [h.2.1 i', mul_zero, zero_mul]
  · intro hp; exact absurd (Finset.mem_univ p) hp

theorem submatrix_succ_mul_of_col (X Y : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (h : ∀ i : Fin n, X i.succ 0 = 0) :
    (X * Y).submatrix Fin.succ Fin.succ =
      X.submatrix Fin.succ Fin.succ * Y.submatrix Fin.succ Fin.succ :=
  submatrix_mul_of_col X Y (p := 0) h

theorem submatrix_succ_mul_of_row (X Y : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (h : ∀ j : Fin n, Y 0 j.succ = 0) :
    (X * Y).submatrix Fin.succ Fin.succ =
      X.submatrix Fin.succ Fin.succ * Y.submatrix Fin.succ Fin.succ :=
  submatrix_mul_of_row X Y (p := 0) h

theorem submatrix_castSucc_mul_of_col (X Y : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (h : ∀ i : Fin n, X i.castSucc (Fin.last n) = 0) :
    (X * Y).submatrix Fin.castSucc Fin.castSucc =
      X.submatrix Fin.castSucc Fin.castSucc * Y.submatrix Fin.castSucc Fin.castSucc := by
  have := submatrix_mul_of_col X Y (p := Fin.last n) (by simpa [Fin.succAbove_last] using h)
  simpa only [Fin.succAbove_last] using this

/-- A matrix fixing `e_p` commutes with the projection killing `e_p`. -/
theorem FixesVertex.commute_proj {X : Matrix (Fin (n + 1)) (Fin (n + 1)) R} {p : Fin (n + 1)}
    (h : FixesVertex X p) : X * (1 - single p p 1) = (1 - single p p 1) * X := by
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul]
  congr 1
  ext i c
  by_cases hi : i = p <;> by_cases hc : c = p
  · subst hi; subst hc; simp
  · subst hi
    obtain ⟨c', rfl⟩ := Fin.exists_succAbove_eq hc
    simp [hc, h.2.2 c']
  · subst hc
    obtain ⟨i', rfl⟩ := Fin.exists_succAbove_eq hi
    simp [hi, h.2.1 i']
  · simp [hi, hc]

end Vertex

section Factor

variable {r : ℕ} {a b : R}

theorem IsChainFactor.apply_row_of_ne {g : Matrix (Fin (r + 1)) (Fin (r + 1)) R} {j : Fin r}
    (h : IsChainFactor g j a b) {i : Fin (r + 1)} (hi₁ : i ≠ j.castSucc) (hi₂ : i ≠ j.succ)
    (c : Fin (r + 1)) : g i c = (1 : Matrix _ _ R) i c := by
  by_cases hc₁ : c = j.castSucc
  · subst hc₁; rw [h.apply_castSucc_of_ne i hi₁ hi₂, one_apply_ne hi₁]
  · by_cases hc₂ : c = j.succ
    · subst hc₂; rw [h.apply_succ, one_apply_ne hi₂]; simp [hi₁]
    · exact h.apply_of_ne i c hc₁ hc₂

theorem IsChainFactor.apply_succ_row {g : Matrix (Fin (r + 1)) (Fin (r + 1)) R} {j : Fin r}
    (h : IsChainFactor g j a b) (c : Fin (r + 1)) :
    g j.succ c = if c = j.castSucc then b else 0 := by
  by_cases hc₁ : c = j.castSucc
  · subst hc₁; simp [h.apply_succ_castSucc]
  · by_cases hc₂ : c = j.succ
    · subst hc₂; rw [h.apply_succ]; simp [(Fin.castSucc_lt_succ).ne']
    · rw [h.apply_of_ne _ _ hc₁ hc₂, one_apply_ne (Ne.symm hc₂)]; simp [hc₁]

theorem IsChainFactor.fixesVertex {g : Matrix (Fin (r + 1)) (Fin (r + 1)) R} {j : Fin r}
    (h : IsChainFactor g j a b) {p : Fin (r + 1)} (hp₁ : p ≠ j.castSucc) (hp₂ : p ≠ j.succ) :
    FixesVertex g p := by
  refine ⟨?_, fun i => ?_, fun c => ?_⟩
  · rw [h.apply_of_ne p p hp₁ hp₂, one_apply_eq]
  · rw [h.apply_of_ne _ p hp₁ hp₂, one_apply_ne (Fin.succAbove_ne p i)]
  · rw [h.apply_row_of_ne hp₁ hp₂, one_apply_ne (Fin.succAbove_ne p c).symm]

theorem IsChainFactor.submatrix_succ {g : Matrix (Fin (r + 2)) (Fin (r + 2)) R} {j : Fin r}
    (h : IsChainFactor g j.succ a b) :
    IsChainFactor (g.submatrix Fin.succ Fin.succ) j a b where
  apply_of_ne i c hc₁ hc₂ := by
    simp only [submatrix_apply]
    rw [h.apply_of_ne _ _ (by rw [← Fin.succ_castSucc]; exact fun e => hc₁ (Fin.succ_injective _ e))
      (fun e => hc₂ (Fin.succ_injective _ e))]
    simp [one_apply]
  apply_succ i := by
    simp only [submatrix_apply]
    rw [h.apply_succ, ← Fin.succ_castSucc]
    simp
  apply_succ_castSucc := by
    simp only [submatrix_apply]
    rw [Fin.succ_castSucc]
    exact h.apply_succ_castSucc
  apply_castSucc_of_ne i hi₁ hi₂ := by
    simp only [submatrix_apply]
    rw [Fin.succ_castSucc]
    exact h.apply_castSucc_of_ne _
      (by rw [← Fin.succ_castSucc]; exact fun e => hi₁ (Fin.succ_injective _ e))
      (fun e => hi₂ (Fin.succ_injective _ e))

theorem IsChainFactor.submatrix_castSucc {g : Matrix (Fin (r + 2)) (Fin (r + 2)) R} {j : Fin r}
    (h : IsChainFactor g j.castSucc a b) :
    IsChainFactor (g.submatrix Fin.castSucc Fin.castSucc) j a b where
  apply_of_ne i c hc₁ hc₂ := by
    simp only [submatrix_apply]
    rw [h.apply_of_ne _ _ (fun e => hc₁ (Fin.castSucc_injective _ e))
      (by rw [Fin.succ_castSucc]; exact fun e => hc₂ (Fin.castSucc_injective _ e))]
    simp [one_apply]
  apply_succ i := by
    simp only [submatrix_apply]
    rw [← Fin.succ_castSucc, h.apply_succ]
    simp
  apply_succ_castSucc := by
    simp only [submatrix_apply]
    rw [← Fin.succ_castSucc]
    exact h.apply_succ_castSucc
  apply_castSucc_of_ne i hi₁ hi₂ := by
    simp only [submatrix_apply]
    exact h.apply_castSucc_of_ne _ (fun e => hi₁ (Fin.castSucc_injective _ e))
      (by rw [Fin.succ_castSucc]; exact fun e => hi₂ (Fin.castSucc_injective _ e))

theorem IsChainFactor.submatrix_succ_of_zero {g : Matrix (Fin (r + 2)) (Fin (r + 2)) R}
    (h : IsChainFactor g 0 a b) :
    g.submatrix Fin.succ Fin.succ = 1 - single 0 0 1 := by
  ext i c
  simp only [submatrix_apply, Matrix.sub_apply]
  by_cases hc : c = 0
  · subst hc
    rw [h.apply_succ]
    by_cases hi : i = 0
    · subst hi; simp
    · simp [one_apply, hi, Ne.symm hi]
  · rw [h.apply_of_ne _ _ (by simp [Fin.succ_ne_zero]) (fun e => hc (Fin.succ_injective _ e))]
    have hc' : ¬(0 : Fin (r + 1)) = c := Ne.symm hc
    simp [one_apply, hc']

theorem IsChainFactor.det_eq : ∀ {r : ℕ} {g : Matrix (Fin (r + 1)) (Fin (r + 1)) R} {j : Fin r},
    IsChainFactor g j a b → g.det = -(a * b)
  | 0, _, j, _ => j.elim0
  | 1, g, j, h => by
    obtain rfl : j = 0 := Subsingleton.elim _ _
    rw [det_fin_two]
    have h01 : g 0 1 = a := by simpa using h.apply_succ 0
    have h11 : g 1 1 = 0 := by simpa using h.apply_succ 1
    have h10 : g 1 0 = b := h.apply_succ_castSucc
    rw [h01, h11, h10]; ring
  | r + 2, g, j, h => by
    by_cases hj : j = 0
    · subst hj
      have hfix : FixesVertex g (Fin.last (r + 2)) :=
        h.fixesVertex (fun e => by have := congrArg Fin.val e; simp at this)
          (fun e => by have := congrArg Fin.val e; simp at this)
      rw [hfix.det_eq, Fin.succAbove_last]
      exact (IsChainFactor.submatrix_castSucc (j := 0) h).det_eq
    · obtain ⟨j', rfl⟩ := Fin.exists_succ_eq.mpr hj
      have hfix : FixesVertex g 0 :=
        h.fixesVertex (fun e => Fin.succ_ne_zero j' (Fin.castSucc_eq_zero_iff.mp e.symm))
          (Fin.succ_ne_zero _).symm
      rw [hfix.det_eq, Fin.succAbove_zero]
      exact h.submatrix_succ.det_eq

end Factor

section Minors

variable {m : ℕ}

/-- Compressing at the bottom vertex: if the projection killing `e_0` is applied first, the
determinant of `1 - (1 - E₀₀) Z` is the bottom-right minor of `1 - Z`. -/
theorem det_one_sub_proj_mul (Z : Matrix (Fin (m + 1)) (Fin (m + 1)) R) :
    (1 - (1 - single 0 0 1) * Z).det = ((1 - Z).submatrix Fin.succ Fin.succ).det := by
  set P : Matrix (Fin (m + 1)) (Fin (m + 1)) R := 1 - single 0 0 1
  have hrow : ∀ k, (P * Z) 0 k = 0 := by
    intro k; simp [P, Matrix.sub_mul, Matrix.sub_apply]
  have hrows : ∀ (i : Fin m) k, (P * Z) i.succ k = Z i.succ k := by
    intro i k; simp [P, Matrix.sub_mul, Matrix.sub_apply, Fin.succ_ne_zero]
  have hM : (1 - P * Z).submatrix Fin.succ Fin.succ = (1 - Z).submatrix Fin.succ Fin.succ := by
    ext i c; simp [Matrix.sub_apply, hrows]
  rw [det_succ_row_zero, Finset.sum_eq_single 0]
  · simp [Matrix.sub_apply, hrow, hM]
  · intro j _ hj
    simp [Matrix.sub_apply, hrow, one_apply_ne (Ne.symm hj)]
  · simp

/-- Expanding at the top vertex: for a chain factor `g` at the top edge and `Z` fixing the top
vertex, `det ((1 - E_top) - g Z) = a * b * det (1 - Z' - E_top')`, where `Z'` is `Z` restricted to
the other vertices. -/
theorem det_proj_sub_mul_of_top {a b : R} {g Z : Matrix (Fin (m + 2)) (Fin (m + 2)) R}
    (hg : IsChainFactor g (Fin.last m) a b) (hZ : FixesVertex Z (Fin.last (m + 1))) :
    ((1 - single (Fin.last (m + 1)) (Fin.last (m + 1)) 1) - g * Z).det =
      a * b * (1 - Z.submatrix Fin.castSucc Fin.castSucc -
        single (Fin.last m) (Fin.last m) 1).det := by
  set L := Fin.last (m + 1)
  set q : Fin (m + 2) := (Fin.last m).castSucc
  have hL : (Fin.last m).succ = L := Fin.succ_last m
  set M := (1 - single L L 1) - g * Z
  have hgZ : ∀ i c, (g * Z) i c = ∑ k, g i k * Z k c := fun i c => mul_apply
  have hcol : ∀ i, M i L = -(if i = q then a else 0) := by
    intro i
    have hsum : (g * Z) i L = g i L := by
      rw [hgZ, Fin.sum_univ_succAbove _ L, hZ.1, mul_one]
      simp [hZ.2.1]
    have hgi : g i L = if i = q then a else 0 := by rw [← hL]; exact hg.apply_succ i
    simp only [M, Matrix.sub_apply, hsum, hgi]
    by_cases hi : i = L
    · subst hi; simp
    · simp [one_apply_ne hi, Matrix.single, Ne.symm hi]
  set Y : Matrix (Fin (m + 1)) (Fin (m + 1)) R := 1 - Z.submatrix Fin.castSucc Fin.castSucc
  have hN : M.submatrix q.succAbove Fin.castSucc =
      updateRow Y (Fin.last m) (b • (Y (Fin.last m) - Pi.single (Fin.last m) 1)) := by
    ext i c
    refine Fin.lastCases ?_ (fun i => ?_) i
    · rw [submatrix_apply, Fin.succAbove_castSucc_self, hL, updateRow_self]
      have hrow : (g * Z) L c.castSucc = b * Z q c.castSucc := by
        rw [hgZ, Finset.sum_eq_single q]
        · rw [← hL, hg.apply_succ_row, ite_eq_left rfl]
        · intro k _ hk
          rw [← hL, hg.apply_succ_row, ite_eq_right hk, zero_mul]
        · simp
      have hLc : L ≠ c.castSucc := (Fin.castSucc_lt_last c).ne'
      have hs : (single L L (1 : R)) L c.castSucc = 0 := by
        simp only [Matrix.single, of_apply]; exact ite_eq_right fun h => hLc h.2
      simp only [M, Y, Matrix.sub_apply, hrow, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
        submatrix_apply, one_apply_ne hLc, hs]
      by_cases hc : c = Fin.last m
      · subst hc; simp [q]
      · simp [one_apply_ne (Ne.symm hc), hc, q]
    · have hi : i.castSucc < Fin.last m := Fin.castSucc_lt_last i
      rw [submatrix_apply, Fin.succAbove_castSucc_of_lt _ _ hi,
        updateRow_ne (Fin.castSucc_lt_last i).ne]
      have hi₁ : i.castSucc.castSucc ≠ (Fin.last m).castSucc :=
        fun e => hi.ne (Fin.castSucc_injective _ e)
      have hi₂ : i.castSucc.castSucc ≠ (Fin.last m).succ := by
        rw [hL]; exact (Fin.castSucc_lt_last _).ne
      have hrow : (g * Z) i.castSucc.castSucc c.castSucc = Z i.castSucc.castSucc c.castSucc := by
        rw [hgZ]
        simp_rw [hg.apply_row_of_ne hi₁ hi₂]
        rw [← mul_apply, Matrix.one_mul]
      have hs : (single L L (1 : R)) i.castSucc.castSucc c.castSucc = 0 := by
        simp only [Matrix.single, of_apply]
        exact ite_eq_right fun h => (Fin.castSucc_lt_last c).ne' h.2
      simp only [M, Y, Matrix.sub_apply, hrow, submatrix_apply, hs]
      simp [one_apply]
  rw [det_succ_column M L, Finset.sum_eq_single q]
  · rw [hcol, ite_eq_left rfl, Fin.succAbove_last, hN, det_updateRow_smul]
    have hY : updateRow Y (Fin.last m) (Y (Fin.last m) - Pi.single (Fin.last m) 1) =
        1 - Z.submatrix Fin.castSucc Fin.castSucc - single (Fin.last m) (Fin.last m) 1 := by
      ext i c
      by_cases hi : i = Fin.last m
      · subst hi; simp [Y, Pi.single_apply, single_apply, eq_comm]
      · rw [updateRow_ne hi]; simp [Y, Ne.symm hi]
    rw [hY]
    have hval : ((q : ℕ) + (L : ℕ)) = 2 * m + 1 := by simp [q, L]; ring
    rw [hval, pow_succ, pow_mul, neg_one_sq, one_pow]
    ring
  · intro i _ hi
    rw [hcol, ite_eq_right hi]; ring
  · simp

end Minors

section List

variable {ι : Type*}

/-- Forget the bottom edge and shift the others down. -/
def predEdge {r : ℕ} (o : Option (Fin (r + 1))) : Option (Fin r) :=
  o.bind fun j => if h : j = 0 then none else some (j.pred h)

theorem predEdge_eq_some {r : ℕ} {o : Option (Fin (r + 1))} {j : Fin r} :
    predEdge o = some j ↔ o = some j.succ := by
  cases o with
  | none => simp [predEdge]
  | some k =>
    by_cases hk : k = 0
    · subst hk; simp [predEdge, (Fin.succ_ne_zero j).symm]
    · simp [predEdge, hk, Fin.pred_eq_iff_eq_succ]

/-- Forget the top edge. -/
def castPredEdge {r : ℕ} (o : Option (Fin (r + 1))) : Option (Fin r) :=
  o.bind fun j => if h : j = Fin.last r then none else some (j.castPred h)

theorem castPredEdge_eq_some {r : ℕ} {o : Option (Fin (r + 1))} {j : Fin r} :
    castPredEdge o = some j ↔ o = some j.castSucc := by
  cases o with
  | none => simp [castPredEdge]
  | some k =>
    by_cases hk : k = Fin.last r
    · subst hk; simp [castPredEdge, (Fin.castSucc_lt_last j).ne']
    · simp [castPredEdge, hk, Fin.castPred_eq_iff_eq_castSucc]

variable {r : ℕ} {F : ι → Matrix (Fin (r + 1)) (Fin (r + 1)) R} {E : ι → Option (Fin r)}
  {a b : Fin r → R}

theorem IsChainList.exists_split {l : List ι} (h : IsChainList l F E a b) (j : Fin r) :
    ∃ l₁ i₀ l₂, l = l₁ ++ i₀ :: l₂ ∧ E i₀ = some j ∧ ∀ i ∈ l₁ ++ l₂, E i ≠ some j := by
  have hc := h.countP_eq_one j
  obtain ⟨i₀, hi₀, hE⟩ : ∃ i ∈ l, E i = some j := by
    have hpos : 0 < l.countP (fun i => E i = some j) := by omega
    simpa using List.countP_pos_iff.mp hpos
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hi₀
  refine ⟨l₁, i₀, l₂, rfl, hE, ?_⟩
  have h0 : (l₁ ++ l₂).countP (fun i => E i = some j) = 0 := by
    rw [List.countP_append, List.countP_cons] at hc
    rw [List.countP_append]
    simp only [hE, decide_true, ite_true] at hc
    omega
  simpa using List.countP_eq_zero.mp h0

end List

section Restrict

variable {ι : Type*} {r : ℕ} {F : ι → Matrix (Fin (r + 2)) (Fin (r + 2)) R}
  {E : ι → Option (Fin (r + 1))} {a b : Fin (r + 1) → R} {l₁ l₂ : List ι} {i₀ : ι}

theorem IsChainList.restrict_succ (h : IsChainList (l₁ ++ i₀ :: l₂) F E a b)
    (hE : E i₀ = some 0) (hne : ∀ i ∈ l₁ ++ l₂, E i ≠ some 0) :
    IsChainList (l₂ ++ l₁) (fun i => (F i).submatrix Fin.succ Fin.succ)
      (fun i => predEdge (E i)) (fun j => a j.succ) (fun j => b j.succ) where
  eq_one i hi hEi := by
    have hi' : i ∈ l₁ ++ l₂ := by simp at hi ⊢; tauto
    have hmem : i ∈ l₁ ++ i₀ :: l₂ := by simp at hi ⊢; tauto
    have hnone : E i = none := by
      cases hEi' : E i with
      | none => rfl
      | some k =>
        rw [hEi'] at hEi
        by_cases hk : k = 0
        · exact absurd (hk ▸ hEi') (hne i hi')
        · simp [predEdge, hk] at hEi
    simp only [h.eq_one i hmem hnone]
    exact submatrix_one _ (Fin.succ_injective _)
  isChainFactor i hi j hEi := by
    have hmem : i ∈ l₁ ++ i₀ :: l₂ := by simp at hi ⊢; tauto
    exact (h.isChainFactor i hmem j.succ (predEdge_eq_some.mp hEi)).submatrix_succ
  countP_eq_one j := by
    have h1 := h.countP_eq_one j.succ
    have hi₀ : ¬E i₀ = some j.succ := by rw [hE]; simp [(Fin.succ_ne_zero j).symm]
    rw [List.countP_congr (q := fun i => decide (E i = some j.succ))
      (fun x _ => by simp [predEdge_eq_some])]
    rw [List.countP_append, List.countP_cons] at h1
    rw [List.countP_append]
    simp only [hi₀, decide_false] at h1
    simp at h1 ⊢
    omega

theorem IsChainList.restrict_castSucc (h : IsChainList (l₁ ++ i₀ :: l₂) F E a b)
    (hE : E i₀ = some (Fin.last r)) (hne : ∀ i ∈ l₁ ++ l₂, E i ≠ some (Fin.last r)) :
    IsChainList (l₂ ++ l₁) (fun i => (F i).submatrix Fin.castSucc Fin.castSucc)
      (fun i => castPredEdge (E i)) (fun j => a j.castSucc) (fun j => b j.castSucc) where
  eq_one i hi hEi := by
    have hi' : i ∈ l₁ ++ l₂ := by simp at hi ⊢; tauto
    have hmem : i ∈ l₁ ++ i₀ :: l₂ := by simp at hi ⊢; tauto
    have hnone : E i = none := by
      cases hEi' : E i with
      | none => rfl
      | some k =>
        rw [hEi'] at hEi
        by_cases hk : k = Fin.last r
        · exact absurd (hk ▸ hEi') (hne i hi')
        · simp [castPredEdge, hk] at hEi
    simp only [h.eq_one i hmem hnone]
    exact submatrix_one _ (Fin.castSucc_injective _)
  isChainFactor i hi j hEi := by
    have hmem : i ∈ l₁ ++ i₀ :: l₂ := by simp at hi ⊢; tauto
    exact (h.isChainFactor i hmem j.castSucc (castPredEdge_eq_some.mp hEi)).submatrix_castSucc
  countP_eq_one j := by
    have h1 := h.countP_eq_one j.castSucc
    have hi₀ : ¬E i₀ = some j.castSucc := by
      rw [hE]; simp [(Fin.castSucc_lt_last j).ne']
    rw [List.countP_congr (q := fun i => decide (E i = some j.castSucc))
      (fun x _ => by simp [castPredEdge_eq_some])]
    rw [List.countP_append, List.countP_cons] at h1
    rw [List.countP_append]
    simp only [hi₀, decide_false] at h1
    simp at h1 ⊢
    omega

end Restrict

theorem submatrix_one_sub {n p : Type*} [DecidableEq n] [DecidableEq p]
    (X : Matrix n n R) {e : p → n} (he : Function.Injective e) :
    (1 - X).submatrix e e = 1 - X.submatrix e e := by
  ext i j
  simp [Matrix.sub_apply, Matrix.one_apply, he.eq_iff]

theorem isUnit_det_prod {n : Type*} [Fintype n] [DecidableEq n] (L : List (Matrix n n R))
    (h : ∀ X ∈ L, IsUnit X.det) : IsUnit L.prod.det := by
  induction L with
  | nil => simp
  | cons X L ih =>
    rw [List.prod_cons, det_mul]
    exact (h X List.mem_cons_self).mul (ih fun Y hY => h Y (List.mem_cons_of_mem X hY))

/-- **The bottom minor.** For a product of chain factors in any order, in which every edge occurs
exactly once, the minor of `1 - R` obtained by deleting the bottom row and column is `1`. -/
theorem det_submatrix_succ_one_sub_prod {ι : Type*} : ∀ {r : ℕ} {l : List ι}
    {F : ι → Matrix (Fin (r + 1)) (Fin (r + 1)) R} {E : ι → Option (Fin r)} {a b : Fin r → R},
    IsChainList l F E a b → ((1 - (l.map F).prod).submatrix Fin.succ Fin.succ).det = 1
  | 0, _, _, _, _, _, _ => det_isEmpty
  | r + 1, l, F, E, a, b, h => by
    obtain ⟨l₁, i₀, l₂, rfl, hE, hne⟩ := h.exists_split 0
    have hmem : ∀ i ∈ l₁ ++ l₂, i ∈ l₁ ++ i₀ :: l₂ := by intro i hi; simp at hi ⊢; tauto
    have hfix : ∀ i ∈ l₁ ++ l₂, FixesVertex (F i) 0 := by
      intro i hi
      cases hEi : E i with
      | none => rw [h.eq_one i (hmem i hi) hEi]; exact fixesVertex_one 0
      | some j =>
        have hj : j ≠ 0 := fun e => hne i hi (by rw [hEi, e])
        exact (h.isChainFactor i (hmem i hi) j hEi).fixesVertex
          (fun e => hj (Fin.castSucc_eq_zero_iff.mp e.symm)) (Fin.succ_ne_zero j).symm
    have hfixL : ∀ L : List ι, (∀ i ∈ L, i ∈ l₁ ++ l₂) →
        ∀ X ∈ L.map F, FixesVertex X 0 := by
      intro L hL X hX
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hX
      exact hfix i (hL i hi)
    have hA := fixesVertex_prod _ (hfixL l₁ fun i hi => by simp [hi])
    have hB := fixesVertex_prod _ (hfixL l₂ fun i hi => by simp [hi])
    have hg := h.isChainFactor i₀ (by simp) 0 hE
    have hprod : ((l₁ ++ i₀ :: l₂).map F).prod =
        (l₁.map F).prod * (F i₀ * (l₂.map F).prod) := by
      simp [List.prod_append]
    have hBA : (l₂.map F).prod * (l₁.map F).prod = ((l₂ ++ l₁).map F).prod := by
      simp [List.prod_append]
    have hsub := submatrix_prod ((l₂ ++ l₁).map F) (p := 0)
      (hfixL (l₂ ++ l₁) fun i hi => by simp at hi ⊢; tauto)
    simp only [Fin.succAbove_zero, List.map_map, Function.comp_def] at hsub
    rw [hprod, submatrix_one_sub _ (Fin.succ_injective _),
      submatrix_succ_mul_of_col _ _ hA.2.1, submatrix_succ_mul_of_row _ _ hB.2.2,
      hg.submatrix_succ_of_zero, det_one_sub_mul_comm, Matrix.mul_assoc,
      ← submatrix_succ_mul_of_col _ _ hB.2.1, hBA, det_one_sub_proj_mul, hsub]
    exact det_submatrix_succ_one_sub_prod (h.restrict_succ hE hne)

/-- **The top corner.** For a product of chain factors in any order, in which every edge occurs
exactly once and all scalars are units, `det (1 - R - E_top) = -∏ j, a j * b j`. -/
theorem det_one_sub_prod_sub_single_last {ι : Type*} : ∀ {r : ℕ} {l : List ι}
    {F : ι → Matrix (Fin (r + 1)) (Fin (r + 1)) R} {E : ι → Option (Fin r)} {a b : Fin r → R},
    IsChainList l F E a b → (∀ j, IsUnit (a j)) → (∀ j, IsUnit (b j)) →
    (1 - (l.map F).prod - single (Fin.last r) (Fin.last r) 1).det = -∏ j, a j * b j
  | 0, l, F, E, a, b, h, _, _ => by
    have hone : (l.map F).prod = 1 := by
      apply List.prod_eq_one
      intro X hX
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hX
      exact h.eq_one i hi (by cases hEi : E i with | none => rfl | some j => exact j.elim0)
    rw [hone, sub_self, zero_sub, det_fin_one]
    simp [Matrix.single]
  | r + 1, l, F, E, a, b, h, ha, hb => by
    obtain ⟨l₁, i₀, l₂, rfl, hE, hne⟩ := h.exists_split (Fin.last r)
    have hmem : ∀ i ∈ l₁ ++ l₂, i ∈ l₁ ++ i₀ :: l₂ := by intro i hi; simp at hi ⊢; tauto
    have hfix : ∀ i ∈ l₁ ++ l₂, FixesVertex (F i) (Fin.last (r + 1)) := by
      intro i hi
      cases hEi : E i with
      | none => rw [h.eq_one i (hmem i hi) hEi]; exact fixesVertex_one _
      | some j =>
        have hj : j ≠ Fin.last r := fun e => hne i hi (by rw [hEi, e])
        exact (h.isChainFactor i (hmem i hi) j hEi).fixesVertex
          (Fin.castSucc_lt_last j).ne' (fun e => hj (Fin.succ_eq_last_succ.mp e.symm))
    have hdet : ∀ i ∈ l₁ ++ l₂, IsUnit (F i).det := by
      intro i hi
      cases hEi : E i with
      | none => rw [h.eq_one i (hmem i hi) hEi, det_one]; exact isUnit_one
      | some j =>
        rw [(h.isChainFactor i (hmem i hi) j hEi).det_eq]
        exact ((ha j).mul (hb j)).neg
    have hfixL : ∀ L : List ι, (∀ i ∈ L, i ∈ l₁ ++ l₂) →
        ∀ X ∈ L.map F, FixesVertex X (Fin.last (r + 1)) := by
      intro L hL X hX
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hX
      exact hfix i (hL i hi)
    set A := (l₁.map F).prod
    set B := (l₂.map F).prod
    have hA : FixesVertex A (Fin.last (r + 1)) :=
      fixesVertex_prod _ (hfixL l₁ fun i hi => by simp [hi])
    have hB : FixesVertex B (Fin.last (r + 1)) :=
      fixesVertex_prod _ (hfixL l₂ fun i hi => by simp [hi])
    have hAdet : IsUnit A.det := isUnit_det_prod _ (by
      intro X hX
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hX
      exact hdet i (by simp [hi]))
    have hg := h.isChainFactor i₀ (by simp) (Fin.last r) hE
    have hprod : ((l₁ ++ i₀ :: l₂).map F).prod = A * (F i₀ * B) := by
      simp [A, B, List.prod_append]
    have hBA : B * A = ((l₂ ++ l₁).map F).prod := by simp [A, B, List.prod_append]
    set P : Matrix (Fin (r + 2)) (Fin (r + 2)) R :=
      1 - single (Fin.last (r + 1)) (Fin.last (r + 1)) 1
    have hconj : P - A * (F i₀ * B) = A * (P - F i₀ * (B * A)) * A⁻¹ := by
      rw [Matrix.mul_sub, Matrix.sub_mul, hA.commute_proj, Matrix.mul_assoc P,
        mul_nonsing_inv _ hAdet, Matrix.mul_one]
      simp only [Matrix.mul_assoc, mul_nonsing_inv _ hAdet, Matrix.mul_one]
    have hZ : FixesVertex (B * A) (Fin.last (r + 1)) := hB.mul hA
    rw [hprod, sub_right_comm, hconj, det_conj ((isUnit_iff_isUnit_det A).mpr hAdet),
      det_proj_sub_mul_of_top hg hZ, hBA]
    have hsub := submatrix_prod ((l₂ ++ l₁).map F) (p := Fin.last (r + 1))
      (hfixL (l₂ ++ l₁) fun i hi => by simp at hi ⊢; tauto)
    simp only [Fin.succAbove_last, List.map_map, Function.comp_def] at hsub
    rw [hsub, det_one_sub_prod_sub_single_last (h.restrict_castSucc hE hne)
      (fun j => ha j.castSucc) (fun j => hb j.castSucc), Fin.prod_univ_castSucc]
    ring

theorem updateRow_sub_single {n : Type*} [Fintype n] [DecidableEq n] (Y : Matrix n n R) (i : n) :
    updateRow Y i (Y i - Pi.single i 1) = Y - single i i 1 := by
  ext a c
  by_cases ha : a = i
  · subst ha; simp [Matrix.single, Pi.single_apply, eq_comm]
  · rw [updateRow_ne ha]; simp [Matrix.single, Ne.symm ha]

section Merged

variable {p q : ℕ}

/-- The merged factor connecting the top vertex `inl (last p)` of a left chain to the bottom vertex
`inr 0` of a right chain: it fixes every other basis vector, sends `e_{inr 0}` to
`lam • e_{inl last}`, and sends `e_{inl last}` into the span of the two, with coefficient `mu` on
`e_{inr 0}`. -/
structure IsMergedFactor (g : Matrix (Fin (p + 1) ⊕ Fin (q + 1)) (Fin (p + 1) ⊕ Fin (q + 1)) R)
    (lam mu : R) : Prop where
  apply_of_ne : ∀ i c, c ≠ Sum.inl (Fin.last p) → c ≠ Sum.inr 0 →
    g i c = (1 : Matrix _ _ R) i c
  apply_inr_zero : ∀ i, g i (Sum.inr 0) = if i = Sum.inl (Fin.last p) then lam else 0
  apply_inr_zero_inl_last : g (Sum.inr 0) (Sum.inl (Fin.last p)) = mu
  apply_inl_last_of_ne : ∀ i, i ≠ Sum.inl (Fin.last p) → i ≠ Sum.inr 0 →
    g i (Sum.inl (Fin.last p)) = 0

variable {g : Matrix (Fin (p + 1) ⊕ Fin (q + 1)) (Fin (p + 1) ⊕ Fin (q + 1)) R} {lam mu : R}

theorem IsMergedFactor.apply_row_of_ne (hg : IsMergedFactor g lam mu)
    {i : Fin (p + 1) ⊕ Fin (q + 1)} (h₁ : i ≠ Sum.inl (Fin.last p)) (h₂ : i ≠ Sum.inr 0)
    (c : Fin (p + 1) ⊕ Fin (q + 1)) : g i c = (1 : Matrix _ _ R) i c := by
  by_cases hc₁ : c = Sum.inl (Fin.last p)
  · subst hc₁; rw [hg.apply_inl_last_of_ne i h₁ h₂, one_apply_ne h₁]
  · by_cases hc₂ : c = Sum.inr 0
    · subst hc₂; rw [hg.apply_inr_zero, one_apply_ne h₂]; simp [h₁]
    · exact hg.apply_of_ne i c hc₁ hc₂

theorem IsMergedFactor.apply_inr_zero_row (hg : IsMergedFactor g lam mu)
    (c : Fin (p + 1) ⊕ Fin (q + 1)) :
    g (Sum.inr 0) c = if c = Sum.inl (Fin.last p) then mu else 0 := by
  by_cases hc₁ : c = Sum.inl (Fin.last p)
  · subst hc₁; simp [hg.apply_inr_zero_inl_last]
  · by_cases hc₂ : c = Sum.inr 0
    · subst hc₂; rw [hg.apply_inr_zero]; simp
    · rw [hg.apply_of_ne _ _ hc₁ hc₂, one_apply_ne (Ne.symm hc₂)]; simp [hc₁]

/-- **The merged cofactor.** For the merged factor `g` and a block-diagonal `T`, the cofactor of
`1 - g T` at `(inr 0, inl last)` is `-mu` times the top corner of the left block and the bottom
minor of the right block. -/
theorem adjugate_one_sub_mergedFactor_mul (hg : IsMergedFactor g lam mu)
    (RL : Matrix (Fin (p + 1)) (Fin (p + 1)) R) (RR : Matrix (Fin (q + 1)) (Fin (q + 1)) R) :
    adjugate (1 - g * fromBlocks RL 0 0 RR) (Sum.inr 0) (Sum.inl (Fin.last p)) =
      -(mu * (1 - RL - single (Fin.last p) (Fin.last p) 1).det *
        ((1 - RR).submatrix Fin.succ Fin.succ).det) := by
  set T := fromBlocks RL 0 0 RR
  set lt : Fin (p + 1) ⊕ Fin (q + 1) := Sum.inl (Fin.last p)
  set z0 : Fin (p + 1) ⊕ Fin (q + 1) := Sum.inr 0
  have hne : z0 ≠ lt := Sum.inr_ne_inl
  have hrow_other : ∀ i, i ≠ lt → i ≠ z0 → ∀ c, (g * T) i c = T i c := by
    intro i h₁ h₂ c
    rw [mul_apply]
    simp_rw [hg.apply_row_of_ne h₁ h₂]
    rw [← mul_apply, Matrix.one_mul]
  have hrow_z0 : ∀ c, (g * T) z0 c = mu * T lt c := by
    intro c
    rw [mul_apply, Finset.sum_eq_single lt]
    · rw [hg.apply_inr_zero_inl_last]
    · intro k _ hk; rw [hg.apply_inr_zero_row, ite_eq_right hk, zero_mul]
    · simp
  rw [adjugate_apply]
  set M1 := (1 - g * T).updateRow lt (Pi.single z0 1)
  rw [← det_updateRow_add_smul_self M1 hne (-1)]
  set M2 := M1.updateRow z0 (M1 z0 + (-1 : R) • M1 lt)
  have hM2z0 : ∀ c, M2 z0 c = -(mu * T lt c) := by
    intro c
    simp only [M2, M1, updateRow_self, updateRow_ne hne, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Matrix.sub_apply, hrow_z0]
    by_cases hc : c = z0
    · subst hc; simp; ring
    · simp [one_apply_ne (Ne.symm hc), hc]
  have hM2lt : ∀ c, M2 lt c = (Pi.single z0 (1 : R) : _ → R) c := by
    intro c; simp [M2, M1]
  have hM2other : ∀ i, i ≠ lt → i ≠ z0 → ∀ c, M2 i c = (1 : Matrix _ _ R) i c - T i c := by
    intro i h₁ h₂ c
    simp only [M2, M1, updateRow_ne h₁, updateRow_ne h₂, Matrix.sub_apply, hrow_other i h₁ h₂]
  have hblocks : M2.submatrix (Equiv.swap lt z0) id =
      fromBlocks (updateRow (1 - RL) (Fin.last p) (fun c => -(mu * RL (Fin.last p) c))) 0 0
        (updateRow (1 - RR) 0 (Pi.single 0 1)) := by
    ext i c
    rcases i with i | i
    · by_cases hi : i = Fin.last p
      · subst hi
        rw [submatrix_apply, Equiv.swap_apply_left, hM2z0]
        rcases c with c | c
        · simp [T, lt]
        · simp [T, lt]
      · have h₁ : (Sum.inl i : Fin (p + 1) ⊕ Fin (q + 1)) ≠ lt := fun e => hi (Sum.inl_injective e)
        have h₂ : (Sum.inl i : Fin (p + 1) ⊕ Fin (q + 1)) ≠ z0 := Sum.inl_ne_inr
        rw [submatrix_apply, Equiv.swap_apply_of_ne_of_ne h₁ h₂, hM2other _ h₁ h₂]
        rcases c with c | c
        · simp [T, updateRow_ne hi, Matrix.sub_apply, one_apply]
        · simp [T]
    · by_cases hi : i = 0
      · subst hi
        rw [submatrix_apply, Equiv.swap_apply_right, hM2lt]
        rcases c with c | c
        · simp [z0]
        · simp [z0, Pi.single_apply]
      · have h₁ : (Sum.inr i : Fin (p + 1) ⊕ Fin (q + 1)) ≠ lt := Sum.inr_ne_inl
        have h₂ : (Sum.inr i : Fin (p + 1) ⊕ Fin (q + 1)) ≠ z0 := fun e => hi (Sum.inr_injective e)
        rw [submatrix_apply, Equiv.swap_apply_of_ne_of_ne h₁ h₂, hM2other _ h₁ h₂]
        rcases c with c | c
        · simp [T]
        · simp [T, updateRow_ne hi, Matrix.sub_apply, one_apply]
  have hswap : (M2.submatrix (Equiv.swap lt z0) id).det = -M2.det := by
    rw [det_permute, Equiv.Perm.sign_swap hne.symm]; simp
  have hL : (updateRow (1 - RL) (Fin.last p) (fun c => -(mu * RL (Fin.last p) c))).det =
      mu * (1 - RL - single (Fin.last p) (Fin.last p) 1).det := by
    have hv : (fun c => -(mu * RL (Fin.last p) c)) =
        mu • ((1 - RL) (Fin.last p) - Pi.single (Fin.last p) 1) := by
      funext c
      by_cases hc : c = Fin.last p
      · subst hc; simp
      · simp [Matrix.sub_apply, one_apply_ne (Ne.symm hc), hc]
    rw [hv, det_updateRow_smul, updateRow_sub_single]
  have hR : (updateRow (1 - RR) 0 (Pi.single 0 1)).det =
      ((1 - RR).submatrix Fin.succ Fin.succ).det := by
    rw [← adjugate_apply, adjugate_fin_succ_eq_det_submatrix]
    simp
  have hM2 : M2.det = -(M2.submatrix (Equiv.swap lt z0) id).det := by rw [hswap, neg_neg]
  rw [hM2, hblocks, det_fromBlocks_zero₂₁, hL, hR]

end Merged

section Middle

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- **The middle vertex.** Let `Q` act on `W` and fix the extra vertex `mid`. Multiply on the left
by the unipotent `(1 + cb E_{mid, z0}) (1 + ca E_{lt, mid})`. Then
`det (1 - U (Q ⊕ 1)) = -(ca * cb * adj (1 - Q) z0 lt)`. -/
theorem det_one_sub_unipotent_mul_fromBlocks (Q : Matrix W W R) {lt z0 : W} (hne : z0 ≠ lt)
    (ca cb : R) :
    (1 - (1 + cb • single (Sum.inr () : W ⊕ Unit) (Sum.inl z0 : W ⊕ Unit) (1 : R)) *
        (1 + ca • single (Sum.inl lt : W ⊕ Unit) (Sum.inr () : W ⊕ Unit) (1 : R)) *
          fromBlocks Q 0 0 (1 : Matrix Unit Unit R)).det =
      -(ca * cb * adjugate (1 - Q) z0 lt) := by
  set mid : W ⊕ Unit := Sum.inr ()
  set lt' : W ⊕ Unit := Sum.inl lt
  set z0' : W ⊕ Unit := Sum.inl z0
  set Q' : Matrix (W ⊕ Unit) (W ⊕ Unit) R := fromBlocks Q 0 0 1
  have hne₀ : z0' ≠ lt' := fun e => hne (Sum.inl_injective e)
  have hne' : lt' ≠ mid := Sum.inl_ne_inr
  set U' : Matrix (W ⊕ Unit) (W ⊕ Unit) R :=
    1 + ca • single lt' mid 1 + cb • single mid z0' 1
  have hU : (1 + cb • single mid z0' (1 : R)) * (1 + ca • single lt' mid 1) = U' := by
    have h0 : single mid z0' (1 : R) * single lt' mid 1 = 0 := by simp [hne₀]
    rw [add_mul, mul_add, mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul,
      smul_mul_smul_comm, h0, smul_zero]
    simp only [U']
    abel
  rw [hU]
  have hUQ : ∀ i c, (U' * Q') i c = Q' i c + (if i = lt' then ca * Q' mid c else 0) +
      (if i = mid then cb * Q' z0' c else 0) := by
    intro i c
    simp only [U', Matrix.add_mul, Matrix.one_mul, Matrix.add_apply, Matrix.smul_mul,
      Matrix.smul_apply, smul_eq_mul]
    congr 1; congr 1
    · by_cases hi : i = lt'
      · subst hi; simp
      · simp [hi]
    · by_cases hi : i = mid
      · subst hi; simp
      · simp [hi]
  have hQ'11 : ∀ x y : W, Q' (Sum.inl x) (Sum.inl y) = Q x y := fun x y => rfl
  have hQ'12 : ∀ x : W, Q' (Sum.inl x) mid = 0 := fun x => rfl
  have hQ'21 : ∀ y : W, Q' mid (Sum.inl y) = 0 := fun y => rfl
  have hQ'22 : Q' mid mid = 1 := rfl
  set N := 1 - U' * Q'
  have hcol : ∀ i, N i mid = if i = lt' then -ca else 0 := by
    intro i
    simp only [N, Matrix.sub_apply]
    rw [hUQ]
    rcases i with x | x
    · rw [hQ'12, hQ'22, one_apply_ne (Sum.inl_ne_inr), ite_eq_right (Sum.inl_ne_inr)]
      by_cases hx : (Sum.inl x : W ⊕ Unit) = lt'
      · rw [ite_eq_left hx, ite_eq_left hx]; ring
      · rw [ite_eq_right hx, ite_eq_right hx]; ring
    · obtain rfl : x = () := rfl
      have hz : Q' z0' mid = 0 := hQ'12 z0
      rw [hQ'22, one_apply_eq, ite_eq_right hne'.symm, ite_eq_left rfl, hz, ite_eq_right hne'.symm]
      ring
  rw [det_eq_sum_mul_adjugate_col N mid, Finset.sum_eq_single lt']
  rotate_left
  · intro i _ hi; rw [hcol, ite_eq_right hi, zero_mul]
  · simp
  rw [hcol, ite_eq_left rfl, adjugate_apply]
  set N1 := N.updateRow lt' (Pi.single mid 1)
  have hN11 : ∀ x y : W, x ≠ lt → N1 (Sum.inl x) (Sum.inl y) = (1 - Q) x y := by
    intro x y hx
    have h₁ : (Sum.inl x : W ⊕ Unit) ≠ lt' := fun e => hx (Sum.inl_injective e)
    simp only [N1, updateRow_ne h₁, N, Matrix.sub_apply]
    rw [hUQ, ite_eq_right h₁, ite_eq_right (Sum.inl_ne_inr), hQ'11]
    simp [one_apply]
  have hN12 : ∀ x : W, x ≠ lt → N1 (Sum.inl x) mid = 0 := by
    intro x hx
    have h₁ : (Sum.inl x : W ⊕ Unit) ≠ lt' := fun e => hx (Sum.inl_injective e)
    simp only [N1, updateRow_ne h₁, N, Matrix.sub_apply]
    rw [hUQ, ite_eq_right h₁, ite_eq_right (Sum.inl_ne_inr), hQ'12,
      one_apply_ne (Sum.inl_ne_inr)]
    ring
  have hN21 : ∀ y : W, N1 mid (Sum.inl y) = -(cb * Q z0 y) := by
    intro y
    simp only [N1, updateRow_ne hne'.symm, N, Matrix.sub_apply]
    rw [hUQ, ite_eq_right hne'.symm, ite_eq_left rfl, hQ'21, hQ'11,
      one_apply_ne (Sum.inr_ne_inl)]
    ring
  have hN22 : N1 mid mid = 0 := by
    simp only [N1, updateRow_ne hne'.symm, N, Matrix.sub_apply]
    rw [hUQ, ite_eq_right hne'.symm, ite_eq_left rfl, hQ'22, hQ'12, one_apply_eq]
    ring
  have hNlt : ∀ c, N1 lt' c = (Pi.single mid (1 : R) : _ → R) c := by
    intro c; simp [N1]
  have hblocks : N1.submatrix (Equiv.swap lt' mid) id =
      fromBlocks (updateRow (1 - Q) lt (fun c => -(cb * Q z0 c))) 0 0 (1 : Matrix Unit Unit R) := by
    ext i c
    rcases i with x | x
    · by_cases hx : x = lt
      · subst hx
        simp only [submatrix_apply, id, lt', Equiv.swap_apply_left]
        rcases c with y | y
        · simp only [hN21, fromBlocks_apply₁₁, updateRow_self]
        · obtain rfl : y = () := rfl
          simp only [fromBlocks_apply₁₂, Matrix.zero_apply]
          exact hN22
      · have h₁ : (Sum.inl x : W ⊕ Unit) ≠ lt' := fun e => hx (Sum.inl_injective e)
        have h₂ : (Sum.inl x : W ⊕ Unit) ≠ mid := Sum.inl_ne_inr
        simp only [submatrix_apply, id, Equiv.swap_apply_of_ne_of_ne h₁ h₂]
        rcases c with y | y
        · simp only [hN11 x y hx, fromBlocks_apply₁₁, updateRow_ne hx]
        · obtain rfl : y = () := rfl
          simp only [fromBlocks_apply₁₂, Matrix.zero_apply]
          exact hN12 x hx
    · obtain rfl : x = () := rfl
      simp only [submatrix_apply, id, mid, Equiv.swap_apply_right, hNlt]
      rcases c with y | y
      · simp [fromBlocks_apply₂₁]
      · obtain rfl : y = () := rfl
        simp [fromBlocks_apply₂₂]
  have hswap : (N1.submatrix (Equiv.swap lt' mid) id).det = -N1.det := by
    rw [det_permute, Equiv.Perm.sign_swap hne']; simp
  have hrow : (fun c => -(cb * Q z0 c)) = (-cb) • (Pi.single z0 1 + (-1 : R) • (1 - Q) z0) := by
    funext c
    by_cases hc : c = z0
    · subst hc; simp [Matrix.sub_apply]
    · simp [Matrix.sub_apply, one_apply_ne (Ne.symm hc), hc]
  have hzero : (updateRow (1 - Q) lt ((1 - Q) z0)).det = 0 :=
    det_zero_of_row_eq hne.symm (by rw [updateRow_self, updateRow_ne hne])
  have hN1 : N1.det = -(fromBlocks (updateRow (1 - Q) lt (fun c => -(cb * Q z0 c))) 0 0
      (1 : Matrix Unit Unit R)).det := by rw [← hblocks, hswap, neg_neg]
  rw [hN1, det_fromBlocks_zero₂₁, det_one, mul_one, hrow, det_updateRow_smul, det_updateRow_add,
    det_updateRow_smul, hzero, ← adjugate_apply]
  ring

end Middle

section Assembly

variable {p q : ℕ} {ι κ : Type*}

/-- **The determinant of the modified chain.** Let `V = (Fin (p + 1) ⊕ Fin (q + 1)) ⊕ Unit` be a
left chain, a right chain and a middle vertex. Let `Q = g (R_L ⊕ R_R)` with `g` the merged factor
and `R_L`, `R_R` products of chain factors in any order, each edge occurring once, and let `Q` fix
the middle vertex. Multiply on the left by the unipotent `(1 + cb E_{mid, inr 0}) (1 + ca E_{inl
last, mid})`. Then `det (1 - U (Q ⊕ 1)) = -(ca * cb * mu * ∏ j, aL j * bL j)`. -/
theorem det_one_sub_unipotent_mul_mergedChain
    {g : Matrix (Fin (p + 1) ⊕ Fin (q + 1)) (Fin (p + 1) ⊕ Fin (q + 1)) R} {lam mu : R}
    (hg : IsMergedFactor g lam mu)
    {lL : List ι} {FL : ι → Matrix (Fin (p + 1)) (Fin (p + 1)) R} {EL : ι → Option (Fin p)}
    {aL bL : Fin p → R} (hL : IsChainList lL FL EL aL bL) (haL : ∀ j, IsUnit (aL j))
    (hbL : ∀ j, IsUnit (bL j))
    {lR : List κ} {FR : κ → Matrix (Fin (q + 1)) (Fin (q + 1)) R} {ER : κ → Option (Fin q)}
    {aR bR : Fin q → R} (hR : IsChainList lR FR ER aR bR) (ca cb : R) :
    (1 - (1 + cb • single (Sum.inr () : (Fin (p + 1) ⊕ Fin (q + 1)) ⊕ Unit)
          (Sum.inl (Sum.inr 0) : (Fin (p + 1) ⊕ Fin (q + 1)) ⊕ Unit) (1 : R)) *
        (1 + ca • single (Sum.inl (Sum.inl (Fin.last p)) : (Fin (p + 1) ⊕ Fin (q + 1)) ⊕ Unit)
          (Sum.inr () : (Fin (p + 1) ⊕ Fin (q + 1)) ⊕ Unit) (1 : R)) *
          fromBlocks (g * fromBlocks (lL.map FL).prod 0 0 (lR.map FR).prod) 0 0
            (1 : Matrix Unit Unit R)).det =
      -(ca * cb * mu * ∏ j, aL j * bL j) := by
  rw [det_one_sub_unipotent_mul_fromBlocks _ Sum.inr_ne_inl ca cb,
    adjugate_one_sub_mergedFactor_mul hg, det_one_sub_prod_sub_single_last hL haL hbL,
    det_submatrix_succ_one_sub_prod hR]
  ring

end Assembly

end Langlands.LinearAlgebra.ChainCoxeter
