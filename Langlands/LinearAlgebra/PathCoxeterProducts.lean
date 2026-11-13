import Langlands.LinearAlgebra.PathCoxeterCoordinates

/-! # Path Coxeter products in arbitrary order, and the pattern block -/

noncomputable section

open Polynomial Matrix

namespace Langlands.LinearAlgebra.PathCoxeter

/-! ### Products with trivial factors removed -/

/-- A product of factors, each of which is `1` or a member of the family `y`, is the product of
the members of `y` that occur. -/
theorem list_prod_map_eq_filterMap {M α : Type*} [Monoid M] (f : α → M) (idx : α → Option ℕ)
    (y : ℕ → M) (h : ∀ a, f a = (idx a).elim 1 y) (l : List α) :
    (l.map f).prod = ((l.filterMap idx).map y).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, ih, h a, List.filterMap_cons]
    cases idx a with
    | none => simp
    | some i => simp

/-- A duplicate-free list whose members are exactly the numbers below `N` is a permutation of
`List.range N`. -/
theorem perm_range_of_nodup {l : List ℕ} {N : ℕ} (hl : l.Nodup) (hmem : ∀ i, i ∈ l ↔ i < N) :
    l.Perm (List.range N) :=
  (List.perm_ext_iff_of_nodup hl List.nodup_range).2 fun i => by rw [hmem, List.mem_range]

variable {R : Type*} [CommRing R] {n : ℕ}

/-! ### Pattern and ordinary factor families -/

/-- The factors of a path product with a block: the simple factors on the lines `i, i+1` for
`i < k`, the block on the lines `k, k+1, k+2` at index `k`, the simple factors on the lines
`i+1, i+2` for `k < i ≤ 2k`, and `1` beyond. -/
def patY (n k : ℕ) (c : ℕ → R) (β : ℕ → ℕ → R) (i : ℕ) : Matrix (Fin n) (Fin n) R :=
  if i < k then sfac n i (c i) else if i = k then core n k β
  else if i ≤ 2 * k then sfac n (i + 1) (c (i + 1)) else 1

/-- The factors of an ordinary path product: the simple factors on the lines `i, i+1` for
`i ≤ 2k+1`, and `1` beyond. -/
def ordY (n k : ℕ) (c : ℕ → R) (i : ℕ) : Matrix (Fin n) (Fin n) R :=
  if i ≤ 2 * k + 1 then sfac n i (c i) else 1

theorem patY_commute {k : ℕ} (hn : n = 2 * k + 3) (c : ℕ → R) (β : ℕ → ℕ → R) (i j : ℕ)
    (hij : i + 2 ≤ j) : Commute (patY n k c β i) (patY n k c β j) := by
  subst hn
  unfold patY
  by_cases hj1 : j < k
  · rw [ite_eq_left (by omega : i < k), ite_eq_left hj1]
    exact sfac_commute_sfac hij (by omega) _ _
  by_cases hj2 : j = k
  · rw [ite_eq_left (by omega : i < k), ite_eq_right hj1, ite_eq_left hj2]
    exact sfac_commute_core (by omega) (by omega) _ _
  rw [ite_eq_right hj1, ite_eq_right hj2]
  by_cases hj3 : j ≤ 2 * k
  · rw [ite_eq_left hj3]
    by_cases hi1 : i < k
    · rw [ite_eq_left hi1]
      exact sfac_commute_sfac (by omega) (by omega) _ _
    by_cases hi2 : i = k
    · rw [ite_eq_right hi1, ite_eq_left hi2]
      exact core_commute_sfac (by omega) (by omega) _ _
    rw [ite_eq_right hi1, ite_eq_right hi2, ite_eq_left (by omega : i ≤ 2 * k)]
    exact sfac_commute_sfac (by omega) (by omega) _ _
  · rw [ite_eq_right hj3]
    exact Commute.one_right _

theorem ordY_commute {k : ℕ} (hn : n = 2 * k + 3) (c : ℕ → R) (i j : ℕ) (hij : i + 2 ≤ j) :
    Commute (ordY n k c i) (ordY n k c j) := by
  subst hn
  unfold ordY
  by_cases hj : j ≤ 2 * k + 1
  · rw [ite_eq_left hj, ite_eq_left (by omega)]
    exact sfac_commute_sfac hij (by omega) _ _
  · rw [ite_eq_right hj]
    exact Commute.one_right _

theorem prod_range_patY (k : ℕ) (c : ℕ → R) (β : ℕ → ℕ → R) :
    ((List.range (2 * k + 1)).map (patY (2 * k + 3) k c β)).prod = pathMat k c β := by
  have h1 : (List.range k).map (patY (2 * k + 3) k c β) =
      (List.range k).map fun i => sfac (2 * k + 3) (0 + i) (c (0 + i)) := by
    apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    simp only [patY, zero_add]
    rw [ite_eq_left hi]
  have h3 : (List.range k).map (patY (2 * k + 3) k c β ∘ fun x => k + 1 + x) =
      (List.range k).map fun i => sfac (2 * k + 3) (k + 2 + i) (c (k + 2 + i)) := by
    apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    simp only [Function.comp_apply, patY]
    rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega),
      show k + 1 + i + 1 = k + 2 + i by omega]
  have h2 : patY (2 * k + 3) k c β k = core (2 * k + 3) k β := by simp [patY]
  rw [show 2 * k + 1 = (k + 1) + k by omega, List.range_add, List.range_succ, List.map_append,
    List.map_append, List.prod_append, List.prod_append, List.map_singleton,
    List.prod_singleton, List.map_map, h1, h2, h3, pathMat, pprod, pprod]

theorem prod_range_ordY (k : ℕ) (c : ℕ → R) :
    ((List.range (2 * k + 2)).map (ordY (2 * k + 3) k c)).prod =
      pprod (2 * k + 3) 0 (2 * k + 2) c := by
  rw [pprod]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  simp only [ordY, zero_add]
  rw [ite_eq_left (by omega)]

/-- **Path products with a block in any order.** For every ordering `l` of `0, …, 2k`, the
product of the factors `patY n k c β` in the order `l` has the characteristic polynomial of
`pathMat k c β`. -/
theorem charpoly_prod_patY {k : ℕ} (hn : n = 2 * k + 3) (c : ℕ → R) (β : ℕ → ℕ → R)
    {l : List ℕ} (hl : l.Perm (List.range (2 * k + 1))) :
    (l.map (patY n k c β)).prod.charpoly = (pathMat k c β).charpoly := by
  subst hn
  rw [charpoly_prod_perm _ (patY_commute rfl c β) hl, prod_range_patY]

/-- **Ordinary path products in any order.** For every ordering `l` of `0, …, 2k+1`, the product
of the simple factors `ordY n k c` in the order `l` has characteristic polynomial
`ordPoly k c`. -/
theorem charpoly_prod_ordY {k : ℕ} (hn : n = 2 * k + 3) (c : ℕ → R) {l : List ℕ}
    (hl : l.Perm (List.range (2 * k + 2))) :
    (l.map (ordY n k c)).prod.charpoly = ordPoly k c := by
  subst hn
  rw [charpoly_prod_perm _ (ordY_commute rfl c) hl, prod_range_ordY, charpoly_pprod_eq_ordPoly]

/-! ### The pattern block -/

/-- A transposition of the lines `i` and `l` with scalars: column `i` is `a e_l`, column `l` is
`b e_i`, and the other columns are those of the identity. -/
def endpointMat (n i l : ℕ) (a b : R) : Matrix (Fin n) (Fin n) R :=
  fun s t => if (t : ℕ) = i then (if (s : ℕ) = l then a else 0)
    else if (t : ℕ) = l then (if (s : ℕ) = i then b else 0)
    else if s = t then 1 else 0

theorem vget_one_add_single_mulVec (i j : Fin n) (c : R) (v : Fin n → R) :
    vget ((1 + Matrix.single i j c) *ᵥ v) =
      fun b => vget v b + if b = (i : ℕ) then c * vget v j else 0 := by
  funext b
  by_cases hb : b < n
  · rw [vget_of_lt _ hb, vget_of_lt _ hb, add_mulVec, one_mulVec, Pi.add_apply, vget_fin]
    congr 1
    simp only [mulVec, dotProduct, Matrix.single_apply]
    by_cases hbi : b = (i : ℕ)
    · have : i = ⟨b, hb⟩ := Fin.ext hbi.symm
      subst this
      simp
    · rw [ite_eq_right hbi]
      apply Finset.sum_eq_zero
      intro x _
      rw [ite_eq_right]
      · ring
      · rintro ⟨h1, -⟩
        exact hbi (congrArg Fin.val h1).symm
  · rw [vget_of_le _ (by omega), vget_of_le _ (by omega), ite_eq_right (by have := i.2; omega),
      add_zero]

theorem vget_endpointMat_mulVec {i l : ℕ} (hil : i ≠ l) (hi : i < n) (hl : l < n) (a b : R)
    (v : Fin n → R) :
    vget (endpointMat n i l a b *ᵥ v) =
      fun s => if s = l then a * vget v i else if s = i then b * vget v l else vget v s := by
  funext s
  by_cases hs : s < n
  · rw [vget_of_lt _ hs, vget_of_lt _ hi, vget_of_lt _ hl, vget_of_lt _ hs]
    simp only [mulVec, dotProduct, endpointMat]
    by_cases hsl : s = l
    · have hsi : s ≠ i := fun h => hil (h ▸ hsl)
      rw [Fintype.sum_eq_single ⟨i, hi⟩]
      · simp [hsl]
      · intro t ht
        have ht' : (t : ℕ) ≠ i := fun h => ht (Fin.ext h)
        split_ifs <;> simp_all [Fin.ext_iff]
    by_cases hsi : s = i
    · rw [Fintype.sum_eq_single ⟨l, hl⟩]
      · simp [hsi, hil, Ne.symm hil]
      · intro t ht
        have ht' : (t : ℕ) ≠ l := fun h => ht (Fin.ext h)
        split_ifs <;> simp_all [Fin.ext_iff]
    simp only [hsl, hsi, ite_false]
    rw [Fintype.sum_eq_single ⟨s, hs⟩]
    · simp [hsl, hsi]
    · intro t ht
      split_ifs <;> simp_all [Fin.ext_iff]
  · rw [vget_of_le _ (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      vget_of_le _ (by omega)]

/-- The diagonal matrix with the entries `τ` at line `i`, `τ'` at line `i + 2`, and `1`
elsewhere. -/
def torusMat (n i : ℕ) (τ τ' : R) : Matrix (Fin n) (Fin n) R :=
  diagonal fun j => if (j : ℕ) = i then τ else if (j : ℕ) = i + 2 then τ' else 1

theorem vget_torusMat_mulVec (i : ℕ) (τ τ' : R) (v : Fin n → R) :
    vget (torusMat n i τ τ' *ᵥ v) =
      fun s => if s = i then τ * vget v i else if s = i + 2 then τ' * vget v (i + 2)
        else vget v s := by
  funext s
  by_cases hs : s < n
  · rw [vget_of_lt _ hs, torusMat, mulVec_diagonal, vget_of_lt _ hs]
    dsimp only
    by_cases h1 : s = i
    · subst h1
      rw [ite_eq_left rfl, ite_eq_left rfl, vget_of_lt _ hs]
    · rw [ite_eq_right h1, ite_eq_right h1]
      by_cases h2 : s = i + 2
      · subst h2
        rw [ite_eq_left rfl, ite_eq_left rfl, vget_of_lt _ hs]
      · rw [ite_eq_right h2, ite_eq_right h2, one_mul]
  · rw [vget_of_le _ (by omega)]
    split_ifs with h1 h2
    · subst h1
      rw [vget_of_le _ (by omega), mul_zero]
    · subst h2
      rw [vget_of_le _ (by omega), mul_zero]
    · rw [vget_of_le _ (by omega)]

/-- The `3 × 3` block `(τ x a, c_a, b τ'), (τ a c_b, 1, 0), (τ a, 0, 0)`. -/
def blockBeta (τ τ' a b x ca cb : R) : ℕ → ℕ → R := fun r s =>
  if r = 0 then (if s = 0 then τ * x * a else if s = 1 then ca else if s = 2 then b * τ' else 0)
  else if r = 1 then (if s = 0 then τ * a * cb else if s = 1 then 1 else 0)
  else if r = 2 then (if s = 0 then τ * a else 0) else 0

/-- **The block of `u_b u_a x_α(s) n_α α^∨(t)`.** -/
theorem block_eq_core {i : ℕ} (hn : i + 3 ≤ n) (τ τ' a b x ca cb : R) :
    (1 + Matrix.single (⟨i + 1, by omega⟩ : Fin n) ⟨i + 2, by omega⟩ cb) *
        (1 + Matrix.single (⟨i, by omega⟩ : Fin n) ⟨i + 1, by omega⟩ ca) *
        (1 + Matrix.single (⟨i, by omega⟩ : Fin n) ⟨i + 2, by omega⟩ x) *
        endpointMat n i (i + 2) a b * torusMat n i τ τ' =
      core n i (blockBeta τ τ' a b x ca cb) := by
  rw [ext_iff_mulVec]
  intro v
  apply vget_injective
  rw [vget_core_mulVec hn]
  simp only [← mulVec_mulVec]
  rw [vget_one_add_single_mulVec, vget_one_add_single_mulVec, vget_one_add_single_mulVec,
    vget_endpointMat_mulVec (by omega) (by omega) (by omega), vget_torusMat_mulVec]
  funext s
  simp only [coreAct, blockBeta]
  by_cases h0 : s = i
  · subst h0
    simp
    ring
  by_cases h1 : s = i + 1
  · subst h1
    simp
    ring
  by_cases h2 : s = i + 2
  · subst h2
    simp
    ring
  · simp only [show ¬(i ≤ s ∧ s < i + 3) by omega, ite_false]
    simp [h0, h1, h2]

/-- **The block of `x_α(s) n_α`.** -/
theorem block_eq_core_false {i : ℕ} (hn : i + 3 ≤ n) (a b x : R) :
    (1 + Matrix.single (⟨i, by omega⟩ : Fin n) ⟨i + 2, by omega⟩ x) * endpointMat n i (i + 2) a b =
      core n i (blockBeta 1 1 a b x 0 0) := by
  rw [← block_eq_core hn]
  have h1 : torusMat n i (1 : R) 1 = 1 := by
    rw [torusMat, ← diagonal_one]
    congr 1
    funext j
    split_ifs <;> rfl
  simp [h1]

/-! ### Coordinates depend only on the relevant values -/

theorem patCoord_congr {k : ℕ} {d d' : ℕ → R} (σ δ : R) (h1 : ∀ i < k, d i = d' i)
    (h2 : ∀ i, k + 2 ≤ i → i ≤ 2 * k + 1 → d i = d' i) (j : ℕ) :
    patCoord k d σ δ j = patCoord k d' σ δ j := by
  have hu : ∀ j, patU k d σ j = patU k d' σ j := by
    intro j
    unfold patU
    split_ifs with ha hb hc hd
    · rfl
    · exact h1 _ (by omega)
    · rfl
    · exact h2 _ (by omega) hd
    · rfl
  simp only [patCoord, hu]

theorem patCoord_map {S : Type*} [CommRing S] (φ : R →+* S) (k : ℕ) (d : ℕ → R) (σ δ : R)
    (j : ℕ) : φ (patCoord k d σ δ j) = patCoord k (fun i => φ (d i)) (φ σ) (φ δ) j := by
  have hu : ∀ j, φ (patU k d σ j) = patU k (fun i => φ (d i)) (φ σ) j := by
    intro j
    unfold patU
    split_ifs <;> simp
  simp only [patCoord, map_add, hu]
  split_ifs <;> simp

theorem ordPoly_congr {k : ℕ} {γ γ' : ℕ → R} (h : ∀ j < 2 * k + 2, γ j = γ' j) :
    ordPoly k γ = ordPoly k γ' := by
  unfold ordPoly
  rw [Finset.sum_congr rfl fun j hj => by rw [h j (Finset.mem_range.1 hj)]]

end Langlands.LinearAlgebra.PathCoxeter
