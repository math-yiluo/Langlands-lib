import Langlands.AlgebraicGeometry.LangWeil.Stepanov.PointBranch
import Langlands.AlgebraicGeometry.LangWeil.Stepanov.DivisibleKernel
import Langlands.AlgebraicGeometry.LangWeil.Stepanov.ResultantDegree
import Langlands.AlgebraicGeometry.LangWeil.Stepanov.FrobeniusIndependence

/-!
# The linear algebra of the Stepanov construction

The unknowns are the coefficients `v(j, k, i, e)` (`j ≤ N`, `k, i < n`, `e ≤ d`) of the
polynomials `B_{jk} = ∑ v(j, k, i, e) X^e Y^i`.  The auxiliary polynomial is
`A = ∑ B_{jk} X^{qj} Y^{qk}`.  The linear conditions are divisibility by `P` of the
polynomials `E1_l = ∑ Q_l(B_{jk}) X^j Y^k` (first kind) or
`E2_{l,k} = g₀ e_{l,k} - e_{l,n-1} ε_k` with `e_{l,k} = ∑_j Q_l(B_{jk}) X^j` and
`ε_k = divX^[k+1] P` (second kind), where `Q_l B` is the coefficient of `S^l` in `sigma P B`.
-/

noncomputable section

universe u

open Polynomial

namespace Langlands.AlgebraicGeometry.LangWeil.Stepanov

variable {F : Type u} [Field F]

local notation "R2" => Polynomial (Polynomial F)

theorem smul_eq_CC_mul (r : F) (P : R2) : r • P = C (C r) * P := by
  rw [Algebra.smul_def, Polynomial.algebraMap_apply, Polynomial.algebraMap_eq]

/-! ### Boxes of `divX` iterates -/

theorem coeff_divX_iterate {R : Type*} [Semiring R] (P : R[X]) (k j : ℕ) :
    (divX^[k] P).coeff j = P.coeff (j + k) := by
  induction k generalizing P with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih, coeff_divX]
    rfl

theorem inBox_divX_iterate {a b : ℤ} {P : R2} (h : InBox a b P) (k : ℕ) :
    InBox a (b - k) (divX^[k] P) := by
  intro j i hji
  rw [coeff_divX_iterate] at hji
  have := h (j + k) i hji
  push_cast at this
  constructor <;> omega

theorem divX_iterate_natDegree (P : R2) : divX^[P.natDegree] P = C P.leadingCoeff := by
  ext j : 1
  rw [coeff_divX_iterate, coeff_C]
  split_ifs with hj
  · subst hj; rw [zero_add]; rfl
  · exact coeff_eq_zero_of_natDegree_lt (by omega)

theorem divX_iterate_map {K : Type*} [CommRing K] (φ : Polynomial F →+* K) (P : R2) (k : ℕ) :
    divX^[k] (P.map φ) = (divX^[k] P).map φ := by
  ext j
  simp [coeff_divX_iterate, coeff_map]

/-! ### The unknowns -/

/-- Index set of the unknown coefficients: `v (j, k, i, e)` is the coefficient of `X^e Y^i` in
`B_{jk}`. -/
abbrev Idx (N n d : ℕ) := Fin (N + 1) × Fin n × Fin n × Fin (d + 1)

/-- `B_{jk}(v) = ∑_{i < n, e ≤ d} v(j, k, i, e) X^e Y^i` (zero if `j > N` or `k ≥ n`). -/
def coefPolyL (N n d j k : ℕ) : (Idx N n d → F) →ₗ[F] R2 where
  toFun v := ∑ t : Idx N n d, if (t.1 : ℕ) = j ∧ (t.2.1 : ℕ) = k then
      C (C (v t) * X ^ (t.2.2.2 : ℕ)) * X ^ (t.2.2.1 : ℕ) else 0
  map_add' v w := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    split_ifs <;> simp [add_mul]
  map_smul' r v := by
    rw [RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    split_ifs
    · simp only [Pi.smul_apply, smul_eq_mul, smul_eq_CC_mul, map_mul]
      ring
    · simp

theorem coefPolyL_apply (N n d j k : ℕ) (v : Idx N n d → F) :
    coefPolyL N n d j k v = ∑ t : Idx N n d, if (t.1 : ℕ) = j ∧ (t.2.1 : ℕ) = k then
      C (C (v t) * X ^ (t.2.2.2 : ℕ)) * X ^ (t.2.2.1 : ℕ) else 0 := rfl

theorem inBox_coefPolyL (N n d j k : ℕ) (v : Idx N n d → F) :
    InBox d (n - 1 : ℕ) (coefPolyL N n d j k v) := by
  rw [coefPolyL_apply]
  apply inBox_sum
  intro t _
  split_ifs
  · have h1 : InBox (t.2.2.2 : ℕ) (0 : ℤ) (C (C (v t) * X ^ (t.2.2.2 : ℕ)) : R2) := by
      rw [map_mul, map_pow]
      simpa using (inBox_C_C (v t)).mul (inBox_C_X.pow (t.2.2.2 : ℕ))
    refine (h1.mul (inBox_X.pow (t.2.2.1 : ℕ))).mono ?_ ?_
    · have := t.2.2.2.2; push_cast; omega
    · have := t.2.2.1.2; push_cast; omega
  · exact inBox_zero _ _

theorem coeff_coeff_coefPolyL (N n d : ℕ) (v : Idx N n d → F) (t : Idx N n d) :
    ((coefPolyL N n d t.1 t.2.1 v).coeff t.2.2.1).coeff t.2.2.2 = v t := by
  classical
  rw [coefPolyL_apply, finsetSum_coeff, finsetSum_coeff, Finset.sum_eq_single t]
  · rw [if_pos ⟨rfl, rfl⟩, coeff_C_mul_X_pow, if_pos rfl, coeff_C_mul_X_pow, if_pos rfl]
  · intro t' _ ht'
    split_ifs with h
    · rw [coeff_C_mul_X_pow]
      split_ifs with h2
      · rw [coeff_C_mul, coeff_X_pow]
        split_ifs with h3
        · exfalso; apply ht'
          obtain ⟨j', k', i', e'⟩ := t'
          obtain ⟨j, k, i, e⟩ := t
          simp only at h h2 h3
          ext <;> simp_all [Fin.ext_iff]
        · simp
      · simp
    · simp
  · simp

theorem exists_coefPolyL_ne_zero (N n d : ℕ) {v : Idx N n d → F} (hv : v ≠ 0) :
    ∃ j ≤ N, ∃ k < n, coefPolyL N n d j k v ≠ 0 := by
  obtain ⟨t, ht⟩ : ∃ t, v t ≠ 0 := by
    by_contra! H
    exact hv (funext H)
  refine ⟨t.1, Nat.lt_succ_iff.mp t.1.2, t.2.1, t.2.1.2, fun h0 => ht ?_⟩
  have := coeff_coeff_coefPolyL N n d v t
  rw [h0] at this
  simpa using this.symm

/-! ### The coefficient maps `Q_l` -/

/-- `Q_l B` is the coefficient of `S^l` in `sigma P B`. -/
def Ql (P : R2) (l : ℕ) : R2 →ₗ[F] R2 where
  toFun B := PowerSeries.coeff l (sigma P B)
  map_add' B B' := by simp
  map_smul' r B := by
    have h : sigma P (C (C r)) = PowerSeries.C (C (C r)) := subst_C_C _ _ r
    rw [smul_eq_CC_mul, map_mul, h, PowerSeries.coeff_C_mul, RingHom.id_apply, smul_eq_CC_mul]

theorem Ql_apply (P : R2) (l : ℕ) (B : R2) : Ql P l B = PowerSeries.coeff l (sigma P B) := rfl

theorem inBox_Ql {m n : ℕ} {P : R2} (hP : InBox m n P) (l : ℕ) {a b : ℤ} {B : R2}
    (hB : InBox a b B) :
    InBox (a + l * (2 * m - 1)) (b + l * (2 * n - 2)) (Ql P l B) :=
  inW_sigma (m := (m : ℤ)) (n := (n : ℤ)) hP hB l

/-! ### The conditions -/

/-- First kind: `E1_l = ∑_{j ≤ N, k < n} Q_l(B_{jk}) X^j Y^k`. -/
def E1L (P : R2) (N n d l : ℕ) : (Idx N n d → F) →ₗ[F] R2 :=
  ∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range n,
    (LinearMap.mulRight F (C (X ^ j) * X ^ k : R2)).comp ((Ql P l).comp (coefPolyL N n d j k))

theorem E1L_apply (P : R2) (N n d l : ℕ) (v : Idx N n d → F) :
    E1L P N n d l v = ∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range n,
      Ql P l (coefPolyL N n d j k v) * (C (X ^ j) * X ^ k) := by
  simp [E1L, mul_assoc]

/-- `e_{l,k} = ∑_{j ≤ N} Q_l(B_{jk}) X^j`. -/
def eL (P : R2) (N n d l k : ℕ) : (Idx N n d → F) →ₗ[F] R2 :=
  ∑ j ∈ Finset.range (N + 1),
    (LinearMap.mulRight F (C (X ^ j) : R2)).comp ((Ql P l).comp (coefPolyL N n d j k))

theorem eL_apply (P : R2) (N n d l k : ℕ) (v : Idx N n d → F) :
    eL P N n d l k v = ∑ j ∈ Finset.range (N + 1), Ql P l (coefPolyL N n d j k v) * C (X ^ j) := by
  simp [eL]

/-- Second kind: `E2_{l,k} = g₀ e_{l,k} - e_{l,n-1} ε_k`, `ε_k = divX^[k+1] P`. -/
def E2L (P : R2) (N n d l k : ℕ) : (Idx N n d → F) →ₗ[F] R2 :=
  (LinearMap.mulLeft F (C P.leadingCoeff : R2)).comp (eL P N n d l k) -
    (LinearMap.mulRight F (divX^[k + 1] P)).comp (eL P N n d l (n - 1))

theorem E2L_apply (P : R2) (N n d l k : ℕ) (v : Idx N n d → F) :
    E2L P N n d l k v =
      C P.leadingCoeff * eL P N n d l k v - eL P N n d l (n - 1) v * divX^[k + 1] P := by
  simp [E2L]

/-! ### Degree boxes of the conditions -/

theorem inBox_Ql_coefPolyL {m n : ℕ} {P : R2} (hP : InBox m n P) (N d l j k : ℕ)
    (v : Idx N n d → F) :
    InBox (d + l * (2 * m - 1)) ((n - 1 : ℕ) + l * (2 * n - 2)) (Ql P l (coefPolyL N n d j k v)) :=
  inBox_Ql hP l (inBox_coefPolyL N n d j k v)

theorem inBox_E1L {m n : ℕ} {P : R2} (hP : InBox m n P) (hn : 1 ≤ n) (N d l : ℕ)
    (v : Idx N n d → F) :
    InBox (d + l * (2 * m - 1) + N) ((n - 1 : ℕ) * (2 * l + 2)) (E1L P N n d l v) := by
  rw [E1L_apply]
  apply inBox_sum
  intro j hj
  apply inBox_sum
  intro k hk
  have hj' := Finset.mem_range.mp hj
  have hk' := Finset.mem_range.mp hk
  have h2 : InBox (j : ℤ) (k : ℤ) (C (X ^ j) * X ^ k : R2) := by
    rw [map_pow]
    simpa using (inBox_C_X.pow j).mul (inBox_X.pow k)
  refine ((inBox_Ql_coefPolyL hP N d l j k v).mul h2).mono ?_ ?_
  · push_cast; omega
  · push_cast [Nat.cast_sub hn]; nlinarith

theorem inBox_eL {m n : ℕ} {P : R2} (hP : InBox m n P) (N d l k : ℕ) (v : Idx N n d → F) :
    InBox (d + l * (2 * m - 1) + N) ((n - 1 : ℕ) + l * (2 * n - 2)) (eL P N n d l k v) := by
  rw [eL_apply]
  apply inBox_sum
  intro j hj
  have hj' := Finset.mem_range.mp hj
  have h2 : InBox (j : ℤ) 0 (C (X ^ j) : R2) := by
    rw [map_pow]
    simpa using inBox_C_X.pow j
  refine ((inBox_Ql_coefPolyL hP N d l j k v).mul h2).mono ?_ ?_
  · push_cast; omega
  · simp

theorem inBox_E2L {m n : ℕ} {P : R2} (hP : InBox m n P) (hn : 1 ≤ n) (N d l k : ℕ)
    (v : Idx N n d → F) :
    InBox (d + l * (2 * m - 1) + N + m) ((n - 1 : ℕ) * (2 * l + 2)) (E2L P N n d l k v) := by
  rw [E2L_apply]
  have hg : InBox (m : ℤ) 0 (C P.leadingCoeff : R2) := by
    intro j i h
    rw [coeff_C] at h
    split_ifs at h with hj
    · subst hj
      refine ⟨?_, le_rfl⟩
      have h1 := le_natDegree_of_ne_zero h
      have h2 := hP P.natDegree i h
      exact h2.1
    · simp at h
  have heps : InBox (m : ℤ) (n - 1 : ℕ) (divX^[k + 1] P) := by
    refine (inBox_divX_iterate hP (k + 1)).mono le_rfl ?_
    push_cast [Nat.cast_sub hn]; omega
  apply InBox.sub
  · refine (hg.mul (inBox_eL hP N d l k v)).mono ?_ ?_
    · push_cast; omega
    · push_cast [Nat.cast_sub hn]; nlinarith
  · refine ((inBox_eL hP N d l (n - 1) v).mul heps).mono ?_ ?_
    · push_cast; omega
    · push_cast [Nat.cast_sub hn]; nlinarith

/-! ### The auxiliary polynomial and its resultant -/

/-- `A(v) = ∑_{j ≤ N, k < n} B_{jk}(v) X^{qj} Y^{qk}`. -/
def normPoly (q N n d : ℕ) (v : Idx N n d → F) : R2 :=
  ∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range n,
    coefPolyL N n d j k v * C (X ^ (q * j)) * X ^ (q * k)

theorem inBox_normPoly (q N n d : ℕ) (hn : 1 ≤ n) (v : Idx N n d → F) :
    InBox (d + q * N : ℕ) ((n - 1) * (q + 1) : ℕ) (normPoly q N n d v) := by
  apply inBox_sum
  intro j hj
  apply inBox_sum
  intro k hk
  have hj' := Finset.mem_range.mp hj
  have hk' := Finset.mem_range.mp hk
  have h1 : InBox ((q * j : ℕ) : ℤ) 0 (C (X ^ (q * j)) : R2) := by
    rw [map_pow]
    simpa using inBox_C_X.pow (q * j)
  have h2 : InBox (0 : ℤ) ((q * k : ℕ) : ℤ) (X ^ (q * k) : R2) := by
    simpa using inBox_X.pow (q * k)
  refine (((inBox_coefPolyL N n d j k v).mul h1).mul h2).mono ?_ ?_
  · push_cast; nlinarith
  · push_cast [Nat.cast_sub hn]
    have : (k : ℤ) ≤ n - 1 := by omega
    nlinarith

theorem normPoly_eq_sum_mul_pow (q N n d : ℕ) (v : Idx N n d → F) :
    normPoly q N n d v = ∑ t ∈ Finset.range (N + 1) ×ˢ Finset.range n,
      coefPolyL N n d t.1 t.2 v * (C (X ^ t.1) * X ^ t.2 : R2) ^ q := by
  rw [normPoly, Finset.sum_product]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
  rw [mul_pow, ← map_pow, ← pow_mul, ← pow_mul, mul_comm j q, mul_comm k q, mul_assoc]

/-- Properties of the resultant `h = Res_Y(P, A(v))` for a nonzero solution `v`. -/
theorem normPoly_resultant [Finite F] (P : R2) (m d N : ℕ) (v : Idx N P.natDegree d → F)
    (hv : v ≠ 0)
    (habs : Irreducible (P.map (Polynomial.mapRingHom (algebraMap F (AlgebraicClosure F)))))
    (hn : 1 ≤ P.natDegree) (hm : ∀ i, (P.coeff i).natDegree ≤ m)
    (hd : P.natDegree * d + m * (P.natDegree - 1) ^ 2 < Nat.card F)
    (hres : ∀ (A : R2) (D : ℕ), A.natDegree ≤ D → ¬ P ∣ A →
      resultant P A P.natDegree D ≠ 0) :
    resultant P (normPoly (Nat.card F) N P.natDegree d v) P.natDegree
        ((P.natDegree - 1) * (Nat.card F + 1)) ≠ 0 ∧
    (resultant P (normPoly (Nat.card F) N P.natDegree d v) P.natDegree
        ((P.natDegree - 1) * (Nat.card F + 1))).natDegree ≤
      (P.natDegree - 1) * (Nat.card F + 1) * m + P.natDegree * (d + Nat.card F * N) ∧
    (normPoly (Nat.card F) N P.natDegree d v).natDegree ≤ (P.natDegree - 1) * (Nat.card F + 1) := by
  have hbox := (inBox_iff_of_nonneg.mp (inBox_normPoly (Nat.card F) N P.natDegree d hn v))
  refine ⟨hres _ _ hbox.1 ?_, resultant_natDegree_le _ _ _ _ _ _ hm hbox.2, hbox.1⟩
  intro hdvd
  obtain ⟨j, hj, k, hk, hne⟩ := exists_coefPolyL_ne_zero N P.natDegree d hv
  have hB := fun j k => inBox_iff_of_nonneg.mp (inBox_coefPolyL N P.natDegree d j k v)
  refine hne (frobeniusIndependence P m d N habs hn hm hd (fun j k => coefPolyL N P.natDegree d j k v)
    (fun j k => by have := (hB j k).1; omega) (fun j k i => (hB j k).2 i) hdvd j hj k hk)

end Langlands.AlgebraicGeometry.LangWeil.Stepanov
