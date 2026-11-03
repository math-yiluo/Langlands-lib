import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Data.Matrix.Mul
import Mathlib.RingTheory.TensorProduct.Basic

/-! # Weight estimate for the generic unitriangular product

The coordinate ring of the upper unitriangular group is a polynomial ring in the
above-diagonal entries `x_ij` (`i < j`). Give `x_ij` the weight `j - i`
(Milne 2017, proof of Theorem 14.5). The comultiplication sends `x_ij` to the
`(i, j)` entry of the product of two generic upper unitriangular matrices. This file
shows that, for a polynomial `f` whose monomials have weight at most `wt m`, the
coefficient of the outer monomial `m` in the comultiplication of `f` is the constant
`f.coeff m`.
-/

noncomputable section

universe u

open MvPolynomial

namespace Langlands.GroupScheme.UnitriangularUnipotent

/-- The positions `(i, j)` with `i < j`, strictly above the diagonal. -/
abbrev Pos (N : ℕ) : Type := {p : Fin N × Fin N // p.1 < p.2}

variable {N : ℕ}

/-- The weight `j - i` of the position `(i, j)`. -/
def posWeight (p : Pos N) : ℕ := p.1.2.val - p.1.1.val

/-- The upper unitriangular matrix whose entry at each position `p` above the diagonal
is `v p`. -/
def upperTri {S : Type*} [CommRing S] (v : Pos N → S) : Matrix (Fin N) (Fin N) S :=
  Matrix.of fun i j => if h : i < j then v ⟨(i, j), h⟩ else (1 : Matrix (Fin N) (Fin N) S) i j

variable (k : Type u) [Field k]

/-- The comultiplication of the polynomial coordinate ring of the upper unitriangular
group: `X p` goes to the `p`-entry of the product of the generic upper unitriangular
matrix in the inner variables (`C (X q)`) with the one in the outer variables (`X q`). -/
def comulPoly :
    MvPolynomial (Pos N) k →ₐ[k] MvPolynomial (Pos N) (MvPolynomial (Pos N) k) :=
  aeval fun p =>
    ((upperTri (S := MvPolynomial (Pos N) (MvPolynomial (Pos N) k)) fun q => C (X q)) *
      upperTri (S := MvPolynomial (Pos N) (MvPolynomial (Pos N) k)) X) p.1.1 p.1.2

theorem one_le_posWeight (p : Pos N) : 1 ≤ posWeight p := by
  have h := p.2
  rw [Fin.lt_def] at h
  simp only [posWeight]
  omega

theorem upperTri_apply_of_lt {S : Type*} [CommRing S] (v : Pos N → S) {i j : Fin N}
    (h : j < i) : upperTri v i j = 0 := by
  simp [upperTri, not_lt.mpr h.le, Matrix.one_apply_ne h.ne']

theorem upperTri_apply_self {S : Type*} [CommRing S] (v : Pos N → S) (i : Fin N) :
    upperTri v i i = 1 := by
  simp [upperTri]

theorem upperTri_apply_of_lt' {S : Type*} [CommRing S] (v : Pos N → S) {i j : Fin N}
    (h : i < j) : upperTri v i j = v ⟨(i, j), h⟩ := by
  simp [upperTri, h]

theorem upperTri_map {S T : Type*} [CommRing S] [CommRing T] (φ : S →+* T) (v : Pos N → S) :
    (upperTri v).map φ = upperTri (fun q => φ (v q)) := by
  ext i j
  rcases lt_trichotomy i j with h | rfl | h
  · simp [upperTri_apply_of_lt' _ h]
  · simp [upperTri_apply_self]
  · simp [upperTri_apply_of_lt _ h]

theorem upperTri_zero {S : Type*} [CommRing S] :
    upperTri (N := N) (fun _ => (0 : S)) = 1 := by
  ext i j
  rcases lt_trichotomy i j with h | rfl | h
  · simp [upperTri_apply_of_lt' _ h, Matrix.one_apply_ne h.ne]
  · simp [upperTri_apply_self]
  · simp [upperTri_apply_of_lt _ h, Matrix.one_apply_ne h.ne']

section TotalWeight

variable {R : Type*} [CommRing R]

/-- A polynomial in the outer variables with coefficients polynomials in the inner
variables has total weight at most `s` if every monomial `d` (outer) times `e` (inner)
occurring in it has `wt d + wt e ≤ s`. -/
def TotalWeightLE (F : MvPolynomial (Pos N) (MvPolynomial (Pos N) R)) (s : ℕ) : Prop :=
  ∀ d e, (F.coeff d).coeff e ≠ 0 →
    Finsupp.weight posWeight d + Finsupp.weight posWeight e ≤ s

namespace TotalWeightLE

variable {F G : MvPolynomial (Pos N) (MvPolynomial (Pos N) R)} {s t : ℕ}

theorem zero (s : ℕ) : TotalWeightLE (0 : MvPolynomial (Pos N) (MvPolynomial (Pos N) R)) s := by
  intro d e h
  simp at h

theorem mono (hF : TotalWeightLE F s) (hst : s ≤ t) : TotalWeightLE F t :=
  fun d e h => (hF d e h).trans hst

theorem add (hF : TotalWeightLE F s) (hG : TotalWeightLE G s) : TotalWeightLE (F + G) s := by
  intro d e h
  simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply] at h
  by_cases hf : (F.coeff d).coeff e = 0
  · rw [hf, zero_add] at h
    exact hG d e h
  · exact hF d e hf

theorem sum {ι : Type*} (I : Finset ι) {F : ι → MvPolynomial (Pos N) (MvPolynomial (Pos N) R)}
    (hF : ∀ i ∈ I, TotalWeightLE (F i) s) : TotalWeightLE (∑ i ∈ I, F i) s := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using zero s
  | insert a I ha ih =>
    rw [Finset.sum_insert ha]
    exact (hF a (Finset.mem_insert_self a I)).add
      (ih fun i hi => hF i (Finset.mem_insert_of_mem hi))

theorem mul (hF : TotalWeightLE F s) (hG : TotalWeightLE G t) :
    TotalWeightLE (F * G) (s + t) := by
  classical
  intro d e h
  rw [coeff_mul, coeff_sum] at h
  obtain ⟨x, hx, hx0⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  rw [coeff_mul] at hx0
  obtain ⟨y, hy, hy0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx0
  have h1 := hF x.1 y.1 (left_ne_zero_of_mul hy0)
  have h2 := hG x.2 y.2 (right_ne_zero_of_mul hy0)
  rw [Finset.mem_antidiagonal] at hx hy
  rw [← hx, ← hy, map_add, map_add]
  omega

theorem C_of {φ : MvPolynomial (Pos N) R}
    (hφ : ∀ e, φ.coeff e ≠ 0 → Finsupp.weight posWeight e ≤ s) : TotalWeightLE (C φ) s := by
  classical
  intro d e h
  rw [coeff_C] at h
  split_ifs at h with hd
  · subst hd
    simpa using hφ e h
  · simp at h

theorem one : TotalWeightLE (1 : MvPolynomial (Pos N) (MvPolynomial (Pos N) R)) 0 := by
  classical
  refine C_of fun e he => ?_
  rw [coeff_one] at he
  split_ifs at he with h
  · subst h; simp
  · exact absurd rfl he

theorem pow (hF : TotalWeightLE F s) (n : ℕ) : TotalWeightLE (F ^ n) (n * s) := by
  induction n with
  | zero => simpa using one
  | succ n ih =>
    rw [pow_succ, Nat.succ_mul]
    exact ih.mul hF

theorem prod {ι : Type*} (I : Finset ι) {F : ι → MvPolynomial (Pos N) (MvPolynomial (Pos N) R)}
    {t : ι → ℕ} (hF : ∀ i ∈ I, TotalWeightLE (F i) (t i)) :
    TotalWeightLE (∏ i ∈ I, F i) (∑ i ∈ I, t i) := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using one
  | insert a I ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact (hF a (Finset.mem_insert_self a I)).mul
      (ih fun i hi => hF i (Finset.mem_insert_of_mem hi))

theorem X_var (q : Pos N) :
    TotalWeightLE (X q : MvPolynomial (Pos N) (MvPolynomial (Pos N) R)) (posWeight q) := by
  classical
  intro d e h
  rw [coeff_X] at h
  split_ifs at h with hd
  · subst hd
    rw [coeff_one] at h
    split_ifs at h with he
    · subst he; simp [Finsupp.weight_single]
    · exact absurd rfl h
  · simp at h

theorem C_X (q : Pos N) :
    TotalWeightLE (C (X q) : MvPolynomial (Pos N) (MvPolynomial (Pos N) R)) (posWeight q) := by
  classical
  refine C_of fun e he => ?_
  rw [coeff_X] at he
  split_ifs at he with h
  · subst h; simp [Finsupp.weight_single]
  · exact absurd rfl he

end TotalWeightLE

theorem totalWeightLE_upperTri_C_X (i l : Fin N) :
    TotalWeightLE
      ((upperTri fun q => (C (X q) : MvPolynomial (Pos N) (MvPolynomial (Pos N) R))) i l)
      (l.val - i.val) := by
  rcases lt_trichotomy i l with h | rfl | h
  · rw [upperTri_apply_of_lt' _ h]
    exact TotalWeightLE.C_X _
  · rw [upperTri_apply_self]
    exact TotalWeightLE.one.mono (Nat.zero_le _)
  · rw [upperTri_apply_of_lt _ h]
    exact TotalWeightLE.zero _

theorem totalWeightLE_upperTri_X (l j : Fin N) :
    TotalWeightLE
      ((upperTri fun q => (X q : MvPolynomial (Pos N) (MvPolynomial (Pos N) R))) l j)
      (j.val - l.val) := by
  rcases lt_trichotomy l j with h | rfl | h
  · rw [upperTri_apply_of_lt' _ h]
    exact TotalWeightLE.X_var _
  · rw [upperTri_apply_self]
    exact TotalWeightLE.one.mono (Nat.zero_le _)
  · rw [upperTri_apply_of_lt _ h]
    exact TotalWeightLE.zero _

end TotalWeight

theorem comulPoly_X (p : Pos N) :
    comulPoly k (X p) =
      ((upperTri (S := MvPolynomial (Pos N) (MvPolynomial (Pos N) k)) fun q => C (X q)) *
        upperTri (S := MvPolynomial (Pos N) (MvPolynomial (Pos N) k)) X) p.1.1 p.1.2 := by
  simp [comulPoly]

theorem totalWeightLE_comulPoly_X (p : Pos N) :
    TotalWeightLE (comulPoly k (X p)) (posWeight p) := by
  rw [comulPoly_X, Matrix.mul_apply]
  refine TotalWeightLE.sum _ fun l _ => ?_
  obtain ⟨⟨i, j⟩, hij⟩ := p
  by_cases hil : l < i
  · rw [upperTri_apply_of_lt _ hil, zero_mul]
    exact TotalWeightLE.zero _
  by_cases hlj : j < l
  · rw [upperTri_apply_of_lt _ hlj, mul_zero]
    exact TotalWeightLE.zero _
  refine ((totalWeightLE_upperTri_C_X i l).mul (totalWeightLE_upperTri_X l j)).mono ?_
  rw [not_lt, Fin.le_def] at hil hlj
  simp only [posWeight]
  omega

theorem totalWeightLE_comulPoly_monomial (a : Pos N →₀ ℕ) (c : k) :
    TotalWeightLE (comulPoly k (monomial a c)) (Finsupp.weight posWeight a) := by
  rw [monomial_eq, map_mul, Finsupp.prod, map_prod, ← zero_add (Finsupp.weight posWeight a)]
  refine TotalWeightLE.mul ?_ ?_
  · rw [comulPoly, aeval_C, algebraMap_apply, algebraMap_eq]
    refine TotalWeightLE.C_of fun e he => ?_
    rw [coeff_C] at he
    split_ifs at he with h
    · subst h; simp
    · exact absurd rfl he
  · rw [Finsupp.weight_apply, Finsupp.sum]
    refine TotalWeightLE.prod _ fun p _ => ?_
    rw [map_pow, smul_eq_mul]
    exact (totalWeightLE_comulPoly_X k p).pow (a p)

theorem totalWeightLE_comulPoly (f : MvPolynomial (Pos N) k) (s : ℕ)
    (hf : ∀ a ∈ f.support, Finsupp.weight posWeight a ≤ s) :
    TotalWeightLE (comulPoly k f) s := by
  rw [f.as_sum, map_sum]
  exact TotalWeightLE.sum _ fun a ha => (totalWeightLE_comulPoly_monomial k a _).mono (hf a ha)

/-- Setting the inner variables to zero undoes the comultiplication. -/
theorem map_constantCoeff_comulPoly (f : MvPolynomial (Pos N) k) :
    map constantCoeff (comulPoly k f) = f := by
  have h : (map (constantCoeff (σ := Pos N) (R := k))).comp (comulPoly k).toRingHom =
      RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [comulPoly, algebraMap_apply]
    · intro p
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, comulPoly_X,
        RingHom.id_apply]
      rw [← Matrix.map_apply (f := map constantCoeff), Matrix.map_mul, upperTri_map,
        upperTri_map]
      simp only [map_C, constantCoeff_X, map_zero, map_X]
      rw [upperTri_zero, one_mul, upperTri_apply_of_lt' _ p.2]
  exact RingHom.congr_fun h f

/-- The coefficient of the outer monomial `m` in the comultiplication of `f` is the constant
`f.coeff m` whenever no monomial of `f` has weight larger than that of `m`. -/
theorem coeff_comulPoly_of_weight_le (f : MvPolynomial (Pos N) k) (m : Pos N →₀ ℕ)
    (hm : ∀ a ∈ f.support, Finsupp.weight posWeight a ≤ Finsupp.weight posWeight m) :
    (comulPoly k f).coeff m = C (f.coeff m) := by
  classical
  have hF := totalWeightLE_comulPoly k f _ hm
  ext e
  rw [coeff_C]
  split_ifs with he
  · subst he
    have h := congrArg (fun F => F.coeff m) (map_constantCoeff_comulPoly k f)
    rwa [coeff_map, constantCoeff_eq] at h
  · by_contra h
    have hle := hF m e h
    obtain ⟨q, hq⟩ : ∃ q, e q ≠ 0 := by
      by_contra! H
      exact he (Finsupp.ext fun q => (H q).symm)
    have h1 := Finsupp.le_weight_of_ne_zero' posWeight hq
    have h2 := one_le_posWeight q
    omega

open scoped TensorProduct in
/-- Applying to the second tensor factor a functional `φ` that picks out the outer monomial
`m` extracts the outer coefficient at `m`. -/
theorem rid_lTensor_eval₂Hom {σ B : Type*} [DecidableEq σ] [CommRing B] [Algebra k B]
    (θ : MvPolynomial σ k →ₐ[k] B) (φ : B →ₗ[k] k) (m : σ →₀ ℕ)
    (hφ : ∀ d, φ (θ (monomial d 1)) = if d = m then 1 else 0)
    (F : MvPolynomial σ (MvPolynomial σ k)) :
    TensorProduct.rid k B (LinearMap.lTensor B φ
      (eval₂Hom ((Algebra.TensorProduct.includeLeft : B →ₐ[k] B ⊗[k] B).toRingHom.comp θ.toRingHom)
        (fun q => (1 : B) ⊗ₜ[k] θ (X q)) F)) = θ (F.coeff m) := by
  classical
  induction F using MvPolynomial.induction_on' with
  | monomial d c =>
    have h1 : (1 : B) ⊗ₜ[k] θ (monomial d 1) = d.prod fun q n => ((1 : B) ⊗ₜ[k] θ (X q)) ^ n := by
      rw [monomial_eq, C_1, one_mul, map_finsuppProd, ← Algebra.TensorProduct.includeRight_apply,
        map_finsuppProd]
      simp [Algebra.TensorProduct.includeRight_apply]
    have key : eval₂Hom
        ((Algebra.TensorProduct.includeLeft : B →ₐ[k] B ⊗[k] B).toRingHom.comp θ.toRingHom)
        (fun q => (1 : B) ⊗ₜ[k] θ (X q)) (monomial d c) = θ c ⊗ₜ[k] θ (monomial d 1) := by
      rw [eval₂Hom_monomial, ← h1]
      simp [Algebra.TensorProduct.tmul_mul_tmul]
    rw [key, LinearMap.lTensor_tmul, TensorProduct.rid_tmul, hφ, coeff_monomial]
    split_ifs <;> simp
  | add p q hp hq =>
    simp only [map_add, hp, hq, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]

end Langlands.GroupScheme.UnitriangularUnipotent
