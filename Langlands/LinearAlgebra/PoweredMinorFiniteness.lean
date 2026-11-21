import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Degree.Operations

/-! # Finite normalized row configurations from powered maximal minors -/

noncomputable section

universe u v w z

open Matrix
open scoped Matrix

namespace Langlands.LinearAlgebra.PoweredMinors

variable {K : Type u} [Field K] {ι : Type v} {J : Type w} [Fintype J] [DecidableEq J]

/-- The square matrix with rows selected by an ordered tuple of labels. -/
def pivot (A : ι → J → K) (p : J → ι) : Matrix J J K := fun k => A (p k)

/-- Normalize every row by the inverse of the same pivot matrix on the right. -/
def normalize (A : ι → J → K) (p : J → ι) : ι → J → K :=
  fun i => A i ᵥ* (pivot A p)⁻¹

/-- The determinant of a selected square matrix, raised to a fixed power. -/
def poweredMinor (n : ℕ) (A : ι → J → K) (p : J → ι) : K := (pivot A p).det ^ n

/-- Cramer's rule computes the normalized entry from a single-row replacement minor. -/
lemma normalize_apply {A : ι → J → K} {p : J → ι} (hA : (pivot A p).det ≠ 0)
    (i : ι) (j : J) :
    normalize A p i j = (pivot A (Function.update p j i)).det / (pivot A p).det := by
  have h := congrFun (Matrix.det_smul_inv_vecMul_eq_cramer_transpose (pivot A p) (A i)
    (isUnit_iff_ne_zero.mpr hA)) j
  rw [Matrix.cramer_transpose_apply] at h
  have hrow : (pivot A p).updateRow j (A i) = pivot A (Function.update p j i) := by
    ext k l
    by_cases hk : k = j <;> simp [Matrix.updateRow_apply, pivot, hk]
  rw [hrow] at h
  apply (eq_div_iff hA).mpr
  have he : (pivot A p).det * normalize A p i j = (pivot A (Function.update p j i)).det := h
  exact (mul_comm _ _).trans he

/-- If two row systems have the same normalization, a single invertible change of
columns carries one row system to the other. -/
lemma exists_right_unit_of_normalize_eq {A B : ι → J → K} {p : J → ι}
    (hA : (pivot A p).det ≠ 0) (hB : (pivot B p).det ≠ 0)
    (h : normalize A p = normalize B p) :
    ∃ G : (Matrix J J K)ˣ, ∀ i, A i ᵥ* (G : Matrix J J K) = B i := by
  have uA : IsUnit (pivot A p).det := isUnit_iff_ne_zero.mpr hA
  have uB : IsUnit (pivot B p).det := isUnit_iff_ne_zero.mpr hB
  let G : (Matrix J J K)ˣ :=
    { val := (pivot A p)⁻¹ * pivot B p
      inv := (pivot B p)⁻¹ * pivot A p
      val_inv := by
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc (pivot B p), Matrix.mul_nonsing_inv _ uB,
          Matrix.one_mul, Matrix.nonsing_inv_mul _ uA]
      inv_val := by
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc (pivot A p), Matrix.mul_nonsing_inv _ uA,
          Matrix.one_mul, Matrix.nonsing_inv_mul _ uB] }
  refine ⟨G, fun i => ?_⟩
  change A i ᵥ* ((pivot A p)⁻¹ * pivot B p) = B i
  rw [← Matrix.vecMul_vecMul]
  change normalize A p i ᵥ* pivot B p = B i
  rw [h, normalize, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ uB, Matrix.vecMul_one]

private lemma finite_pow_roots (n : ℕ) (hn : 0 < n) (c : K) : Finite {x : K // x ^ n = c} := by
  have h := Polynomial.finite_setOfPred_isRoot (Polynomial.X_pow_sub_C_ne_zero hn c)
  have hEq : {x : K | x ^ n = c} = {x | Polynomial.IsRoot (Polynomial.X ^ n - Polynomial.C c) x} := by
    ext x
    simp [Polynomial.IsRoot, sub_eq_zero]
  exact (hEq ▸ h : Set.Finite {x : K | x ^ n = c}).to_subtype

/-- A fibre of the projective powered-minor data admits a finite set of representatives
up to one invertible source change of coordinates. The family may be empty. The common
pivot is assumed to be nonzero in the fixed powered-minor data. -/
theorem exists_finset_of_projectively_equal_poweredMinors [Finite ι] {T : Type z}
    (A : T → ι → J → K) (n : ℕ) (hn : 0 < n) (p : J → ι) (c : (J → ι) → K)
    (hc : c p ≠ 0) (hA : ∀ t, ∃ a : K, a ≠ 0 ∧ ∀ q, poweredMinor n (A t) q = a * c q) :
    ∃ R : Finset T, ∀ t, ∃ t' ∈ R,
      ∃ G : (Matrix J J K)ˣ, ∀ i, A t i ᵥ* (G : Matrix J J K) = A t' i := by
  classical
  choose a ha hp using hA
  have hpivot (t : T) : (pivot (A t) p).det ≠ 0 := by
    have h := hp t p
    unfold poweredMinor at h
    intro hz
    rw [hz, zero_pow hn.ne'] at h
    exact mul_ne_zero (ha t) hc h.symm
  let v (i : ι) (j : J) := c (Function.update p j i) / c p
  have hnorm (t : T) (i : ι) (j : J) : normalize (A t) p i j ^ n = v i j := by
    rw [normalize_apply (hpivot t), div_pow]
    change poweredMinor n (A t) _ / poweredMinor n (A t) _ = _
    rw [hp t, hp t, mul_div_mul_left _ _ (ha t)]
  let E := ∀ i j, {x : K // x ^ n = v i j}
  have (i : ι) (j : J) : Finite {x : K // x ^ n = v i j} := finite_pow_roots n hn (v i j)
  have : Finite E := inferInstanceAs (Finite (∀ i j, {x : K // x ^ n = v i j}))
  let f : T → E := fun t i j => ⟨normalize (A t) p i j, hnorm t i j⟩
  let lift : Set.range f → T := fun x => Classical.choose x.property
  have hlift (x : Set.range f) : f (lift x) = x.val := Classical.choose_spec x.property
  let _ : Fintype (Set.range f) := Fintype.ofFinite _
  refine ⟨Finset.univ.image lift, fun t => ?_⟩
  let x : Set.range f := ⟨f t, Set.mem_range_self t⟩
  refine ⟨lift x, Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩, ?_⟩
  apply exists_right_unit_of_normalize_eq (hpivot t) (hpivot (lift x))
  funext i j
  exact congrArg (fun y : E => (y i j).val) (hlift x).symm

end Langlands.LinearAlgebra.PoweredMinors
