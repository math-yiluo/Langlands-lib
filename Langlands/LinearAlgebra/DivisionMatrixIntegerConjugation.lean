import Mathlib.RingTheory.Valuation.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Integral matrices over a valued division ring are conjugate to matrices of integers

Let `D` be a division ring with a valuation `v`, possibly noncommutative, and let `Y` be a square
matrix over `D`. Let `r > 0`, and suppose that the combinations `∑_{i < r} xᵢ ᵥ* Y ^ i` of the
rows of `Y ^ 0, …, Y ^ (r - 1)`, with coefficients of value at most one, form a set stable under
right multiplication by `Y`. This set contains the standard row vectors, the rows of
`Y ^ 0 = 1`. Then `Y` is conjugate by an invertible matrix to a matrix all of whose entries have
value at most one. The hypothesis `r > 0` is needed: for `r = 0` the set is `{0}`, which is stable
under every `Y`, while the `1 × 1` matrix `Y = [1/2]` over `ℚ₂` with the `2`-adic valuation is
conjugate only to itself.

The general form `exists_units_conj_integral` requires a set `rowSpan v W₀` that contains the
standard row vectors and is stable under right multiplication by `Y`. The form
`exists_units_conj_integral_of_aeval` applies to a root `Y` of a monic polynomial `p` over a
field `F` whose coefficients have values at most one in `D`, with `r` the degree of `p`. If `p`
is constant, then `p = 1`, so `1 = 0` in the matrix ring, the matrix ring is trivial and the
conclusion holds with `u = 1`; otherwise `r > 0` and `Y ^ r = -∑_{j < r} p_j • Y ^ j` gives the
stability.

The proof uses the set `rowSpan v W` of combinations `x ᵥ* W` of the rows of a matrix `W` with
coefficients of value at most one. A generating matrix with the least number of rows has
`D`-linearly independent rows: from a relation `a ᵥ* W = 0` one divides by the coefficient of
largest value and removes the corresponding row (`exists_rowSpan_eq_of_relation`). Its rows
then form an invertible matrix `W` with `W * Y * W⁻¹` integral (`exists_units_conj_integral`).
-/

noncomputable section

open Matrix Polynomial

namespace Langlands.LinearAlgebra.DivisionMatrixIntegerConjugation

variable {D : Type*} [DivisionRing D] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  (v : Valuation D Γ₀)

/-- The left combinations `x ᵥ* W`, with coefficients `x i` of value at most one, of the rows
of a matrix `W`. -/
def rowSpan {m n : ℕ} (W : Matrix (Fin m) (Fin n) D) : Set (Fin n → D) :=
  {y | ∃ x : Fin m → D, (∀ i, v (x i) ≤ 1) ∧ x ᵥ* W = y}

variable {v}

theorem row_mem_rowSpan {m n : ℕ} (W : Matrix (Fin m) (Fin n) D) (i : Fin m) :
    W i ∈ rowSpan v W := by
  classical
  refine ⟨Pi.single i 1, fun j => ?_, ?_⟩
  · by_cases h : j = i
    · subst h
      simp
    · simp [h]
  · rw [single_one_vecMul]
    rfl

theorem zero_mem_rowSpan {m n : ℕ} (W : Matrix (Fin m) (Fin n) D) : 0 ∈ rowSpan v W :=
  ⟨0, fun _ => by simp, zero_vecMul W⟩

theorem add_mem_rowSpan {m n : ℕ} {W : Matrix (Fin m) (Fin n) D} {y z : Fin n → D}
    (hy : y ∈ rowSpan v W) (hz : z ∈ rowSpan v W) : y + z ∈ rowSpan v W := by
  obtain ⟨x, hx, rfl⟩ := hy
  obtain ⟨x', hx', rfl⟩ := hz
  exact ⟨x + x', fun i => (v.map_add _ _).trans (max_le (hx i) (hx' i)), add_vecMul W x x'⟩

theorem smul_mem_rowSpan {m n : ℕ} {W : Matrix (Fin m) (Fin n) D} {y : Fin n → D} {c : D}
    (hc : v c ≤ 1) (hy : y ∈ rowSpan v W) : c • y ∈ rowSpan v W := by
  obtain ⟨x, hx, rfl⟩ := hy
  refine ⟨c • x, fun i => ?_, smul_vecMul c x W⟩
  simp only [Pi.smul_apply, smul_eq_mul, map_mul]
  exact mul_le_one' hc (hx i)

theorem sum_mem_rowSpan {m n : ℕ} {W : Matrix (Fin m) (Fin n) D} {ι : Type*} (s : Finset ι)
    {y : ι → Fin n → D} (hy : ∀ i ∈ s, y i ∈ rowSpan v W) : ∑ i ∈ s, y i ∈ rowSpan v W := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero_mem_rowSpan W
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact add_mem_rowSpan (hy a (Finset.mem_insert_self a s))
      (ih fun i hi => hy i (Finset.mem_insert_of_mem hi))

/-- If the rows of `W` satisfy a nontrivial left relation `a ᵥ* W = 0`, then one row can be
removed without changing `rowSpan v W`: divide `a` by its coefficient of largest value and
remove the corresponding row. -/
theorem exists_rowSpan_eq_of_relation {m n : ℕ} (W : Matrix (Fin (m + 1)) (Fin n) D)
    (a : Fin (m + 1) → D) (ha : a ≠ 0) (haW : a ᵥ* W = 0) :
    ∃ W' : Matrix (Fin m) (Fin n) D, rowSpan v W' = rowSpan v W := by
  classical
  obtain ⟨i₀, -, hi₀⟩ :=
    Finset.exists_max_image Finset.univ (fun i => v (a i)) Finset.univ_nonempty
  have ha₀ : a i₀ ≠ 0 := by
    intro h
    apply ha
    funext i
    have hle := hi₀ i (Finset.mem_univ i)
    rw [h, map_zero] at hle
    exact v.zero_iff.1 (le_antisymm hle zero_le)
  let b : Fin (m + 1) → D := (a i₀)⁻¹ • a
  have hb₀ : b i₀ = 1 := by simp [b, ha₀]
  have hb : ∀ i, v (b i) ≤ 1 := by
    intro i
    have h0 : v (a i₀) ≠ 0 := (v.ne_zero_iff).2 ha₀
    simp only [b, Pi.smul_apply, smul_eq_mul, map_mul, map_inv₀]
    rw [inv_mul_le_iff₀ (zero_lt_iff.2 h0), mul_one]
    exact hi₀ i (Finset.mem_univ i)
  have hbW : b ᵥ* W = 0 := by
    simp only [b, smul_vecMul, haW, smul_zero]
  refine ⟨fun j => W (i₀.succAbove j), ?_⟩
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨Fin.insertNth i₀ 0 x, fun i => ?_, ?_⟩
    · rcases Fin.eq_self_or_eq_succAbove i₀ i with rfl | ⟨j, rfl⟩
      · simp
      · rw [Fin.insertNth_apply_succAbove]
        exact hx j
    · funext j
      simp only [vecMul, dotProduct]
      rw [Fin.sum_univ_succAbove _ i₀]
      simp
  · rintro ⟨x, hx, rfl⟩
    let z : Fin (m + 1) → D := x - x i₀ • b
    have hz0 : z i₀ = 0 := by simp [z, hb₀]
    have hz : z ᵥ* W = x ᵥ* W := by
      simp only [z, sub_vecMul, smul_vecMul, hbW, smul_zero, sub_zero]
    refine ⟨fun j => z (i₀.succAbove j), fun j => ?_, ?_⟩
    · simp only [z, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      refine (v.map_sub _ _).trans (max_le (hx _) ?_)
      rw [map_mul]
      exact mul_le_one' (hx _) (hb _)
    · rw [← hz]
      funext j
      simp only [vecMul, dotProduct]
      rw [Fin.sum_univ_succAbove _ i₀, hz0, zero_mul, zero_add]

/-- **Integral conjugation.** Let `L = rowSpan v W₀` contain the standard row vectors and be
stable under right multiplication by `Y`. Then some invertible matrix `u` makes every entry of
`u * Y * u⁻¹` of value at most one. -/
theorem exists_units_conj_integral {n m₀ : ℕ} (Y : Matrix (Fin n) (Fin n) D)
    (W₀ : Matrix (Fin m₀) (Fin n) D)
    (hbasis : ∀ k : Fin n, Pi.single k 1 ∈ rowSpan v W₀)
    (hY : ∀ y ∈ rowSpan v W₀, y ᵥ* Y ∈ rowSpan v W₀) :
    ∃ u : (Matrix (Fin n) (Fin n) D)ˣ,
      ∀ i j, v (((u : Matrix (Fin n) (Fin n) D) * Y * ((u⁻¹ : (Matrix (Fin n) (Fin n) D)ˣ) :
        Matrix (Fin n) (Fin n) D)) i j) ≤ 1 := by
  classical
  have hP : ∃ m : ℕ, ∃ W : Matrix (Fin m) (Fin n) D, rowSpan v W = rowSpan v W₀ :=
    ⟨m₀, W₀, rfl⟩
  obtain ⟨m, W, hW, hmin⟩ : ∃ m : ℕ, ∃ W : Matrix (Fin m) (Fin n) D,
      rowSpan v W = rowSpan v W₀ ∧
      ∀ m' < m, ∀ W' : Matrix (Fin m') (Fin n) D, rowSpan v W' ≠ rowSpan v W₀ := by
    obtain ⟨W, hW⟩ := Nat.find_spec hP
    exact ⟨Nat.find hP, W, hW, fun m' hm' W' hW' => Nat.find_min hP hm' ⟨W', hW'⟩⟩
  -- The rows of a minimal generating matrix are linearly independent.
  have hind : ∀ a : Fin m → D, a ᵥ* W = 0 → a = 0 := by
    intro a haW
    by_contra ha
    rcases m with _ | m
    · exact ha (funext fun i => i.elim0)
    · obtain ⟨W', hW'⟩ := exists_rowSpan_eq_of_relation (v := v) W a ha haW
      exact hmin m (Nat.lt_succ_self m) W' (hW'.trans hW)
  -- Coordinates of the standard row vectors.
  have hX : ∀ k : Fin n, ∃ x : Fin m → D, (∀ i, v (x i) ≤ 1) ∧ x ᵥ* W = Pi.single k 1 := by
    intro k
    have hk := hbasis k
    rw [← hW] at hk
    exact hk
  choose X₀ _ hXk using hX
  let X : Matrix (Fin n) (Fin m) D := X₀
  have hXW : X * W = 1 := by
    ext k j
    change (X₀ k ᵥ* W) j = _
    rw [hXk k, Matrix.one_apply, Pi.single_apply]
    by_cases h : j = k
    · simp [h]
    · simp [h, Ne.symm h]
  -- The matrix of right multiplication by `Y` in the rows of `W`.
  have hC : ∀ i : Fin m, ∃ c : Fin m → D, (∀ j, v (c j) ≤ 1) ∧ c ᵥ* W = W i ᵥ* Y := by
    intro i
    have hi : W i ᵥ* Y ∈ rowSpan v W₀ := hY _ (hW ▸ row_mem_rowSpan W i)
    rw [← hW] at hi
    exact hi
  choose C₀ hC₁ hC₂ using hC
  let C : Matrix (Fin m) (Fin m) D := C₀
  have hWY : W * Y = C * W := by
    ext i j
    change (W i ᵥ* Y) j = (C₀ i ᵥ* W) j
    rw [hC₂ i]
  have hWX : W * X = 1 := by
    have hrow : ∀ i, ((W * X - 1 : Matrix (Fin m) (Fin m) D) i) ᵥ* W = 0 := by
      intro i
      have h0 : (W * X - 1) * W = 0 := by
        rw [Matrix.sub_mul, Matrix.mul_assoc, hXW, Matrix.mul_one, Matrix.one_mul, sub_self]
      exact congrFun h0 i
    ext i j
    have := congrFun (hind _ (hrow i)) j
    simpa [sub_eq_zero] using this
  -- The number of rows is `n`.
  let e : (Fin m → D) ≃ₗ[D] (Fin n → D) :=
    { toFun := fun x => x ᵥ* W
      invFun := fun y => y ᵥ* X
      map_add' := fun x y => add_vecMul W x y
      map_smul' := fun c x => smul_vecMul c x W
      left_inv := fun x => by simp [vecMul_vecMul, hWX]
      right_inv := fun y => by simp [vecMul_vecMul, hXW] }
  have hmn : m = n := by
    simpa [Module.finrank_fin_fun] using e.finrank_eq
  subst hmn
  refine ⟨⟨W, X, hWX, hXW⟩, fun i j => ?_⟩
  change v ((W * Y * X) i j) ≤ 1
  rw [hWY, Matrix.mul_assoc, hWX, Matrix.mul_one]
  exact hC₁ i j

/-- **Integral conjugation for a root of a monic polynomial.** Let `D` be an algebra over a field
`F`, and let `Y` be a square matrix over `D` annihilated by a monic polynomial over `F` whose
coefficients have values at most one in `D`. Then some invertible matrix `u` makes every entry of
`u * Y * u⁻¹` of value at most one. -/
theorem exists_units_conj_integral_of_aeval {F : Type*} [Field F] [Algebra F D] {n : ℕ}
    (Y : Matrix (Fin n) (Fin n) D) (p : F[X]) (hp : p.Monic)
    (hcoeff : ∀ i, v (algebraMap F D (p.coeff i)) ≤ 1) (hY : aeval Y p = 0) :
    ∃ u : (Matrix (Fin n) (Fin n) D)ˣ,
      ∀ i j, v (((u : Matrix (Fin n) (Fin n) D) * Y * ((u⁻¹ : (Matrix (Fin n) (Fin n) D)ˣ) :
        Matrix (Fin n) (Fin n) D)) i j) ≤ 1 := by
  classical
  set r := p.natDegree with hr
  rcases Nat.eq_zero_or_pos r with hr0 | hrpos
  · -- A monic constant polynomial is `1`, so the matrix ring is trivial.
    have hp1 : p = 1 := Polynomial.eq_one_of_monic_natDegree_zero hp hr0
    have h10 : (1 : Matrix (Fin n) (Fin n) D) = 0 := by simpa [hp1] using hY
    refine ⟨1, fun i j => ?_⟩
    have hz : ∀ M : Matrix (Fin n) (Fin n) D, M = 0 := fun M => by
      rw [← Matrix.mul_one M, h10, Matrix.mul_zero]
    rw [hz ((1 : (Matrix (Fin n) (Fin n) D)ˣ) * Y * ((1⁻¹ : (Matrix (Fin n) (Fin n) D)ˣ) :
      Matrix (Fin n) (Fin n) D))]
    simp
  -- The rows of the powers `Y ^ i`, `i < r`, generate the lattice.
  let g : Fin r × Fin n → Fin n → D := fun ik => (Y ^ (ik.1 : ℕ)) ik.2
  let W₀ : Matrix (Fin (r * n)) (Fin n) D := fun l => g (finProdFinEquiv.symm l)
  have hgen : ∀ (i : ℕ) (hi : i < r) (k : Fin n), (Y ^ i) k ∈ rowSpan v W₀ := by
    intro i hi k
    have h := row_mem_rowSpan (v := v) W₀ (finProdFinEquiv (⟨i, hi⟩, k))
    have hW₀ : W₀ (finProdFinEquiv (⟨i, hi⟩, k)) = (Y ^ i) k := by
      simp only [W₀, g, Equiv.symm_apply_apply]
    rwa [hW₀] at h
  refine exists_units_conj_integral Y W₀ (fun k => ?_) ?_
  · have h := hgen 0 hrpos k
    have h1 : (Y ^ 0) k = Pi.single k 1 := by
      funext j
      simp [Matrix.one_apply, Pi.single_apply, eq_comm]
    rwa [h1] at h
  · -- Right multiplication by `Y` preserves the lattice.
    have hrow : ∀ (i : ℕ) (hi : i < r) (k : Fin n), (Y ^ i) k ᵥ* Y ∈ rowSpan v W₀ := by
      intro i hi k
      have hYi : (Y ^ i) k ᵥ* Y = (Y ^ (i + 1)) k := by
        rw [pow_succ]
        rfl
      rw [hYi]
      rcases Nat.lt_or_ge (i + 1) r with h | h
      · exact hgen (i + 1) h k
      · have hir : i + 1 = r := le_antisymm hi h
        rw [hir]
        -- `Y ^ r = - ∑_{j < r} p_j Y ^ j`.
        have hsum : Y ^ r = -∑ j ∈ Finset.range r, p.coeff j • Y ^ j := by
          have h0 := hY
          rw [hp.as_sum, map_add, map_sum] at h0
          simp only [map_pow, aeval_X, aeval_mul, aeval_C, Algebra.algebraMap_eq_smul_one,
            smul_mul_assoc, one_mul] at h0
          rw [← hr] at h0
          exact eq_neg_of_add_eq_zero_left h0
        have hrow' : (Y ^ r) k = ∑ j ∈ Finset.range r,
            (-(algebraMap F D (p.coeff j))) • (Y ^ j) k := by
          rw [hsum]
          funext l
          simp only [Matrix.neg_apply, Matrix.sum_apply, Matrix.smul_apply, Finset.sum_apply,
            Pi.smul_apply, smul_eq_mul]
          simp only [Algebra.smul_def, neg_mul, Finset.sum_neg_distrib]
        rw [hrow']
        refine sum_mem_rowSpan _ fun j hj => smul_mem_rowSpan ?_ (hgen j
          (Finset.mem_range.1 hj) k)
        rw [Valuation.map_neg]
        exact hcoeff j
    rintro y ⟨x, hx, rfl⟩
    rw [vecMul_vecMul]
    -- Express `x ᵥ* (W₀ * Y)` as a combination of rows of `W₀ * Y`.
    have hexp : x ᵥ* (W₀ * Y) = ∑ l, x l • ((W₀ * Y) l) := by
      funext j
      simp [vecMul, dotProduct, Finset.sum_apply]
    rw [hexp]
    refine sum_mem_rowSpan _ fun l _ => smul_mem_rowSpan (hx l) ?_
    change W₀ l ᵥ* Y ∈ rowSpan v W₀
    exact hrow _ (finProdFinEquiv.symm l).1.isLt _

end Langlands.LinearAlgebra.DivisionMatrixIntegerConjugation
