import Langlands.Representation.Archimedean.ComplexHolomorphicIntertwining

/-!
# Test functions with prescribed holomorphic jets

For level data `(h, b, dτ)` and exponents `γ : Lw n → ℕ`, `testFun h b dτ γ` is the level product
with `J_m = Σ_{k < m} γ_{m k}` extra pairs of determinant factors at the level `m`: the extra
holomorphic factors are `levelDet m (selCol m k)`, which equal `v_{m k}` on the lower unipotent
group (`levelDet_selCol`), `γ_{m k}` times each; all other factors equal `1` there. Hence
(`testFun_nbUnit`) `testFun (nbUnit v) = ∏_m T_m(v)^{σ_m - J_m} · ∏_p v_p^{γ_p}` with the Gram
exponents `σ = gramExp h b dτ`, and `testFun` has the jet `ιP (∏_p X_p^{γ_p})`
(`hasJet_testFun`). If the level data telescope to `χ`, `testFun` is a `U(n)`-finite
principal-series function (`testFun_mem_kFiniteFunctions`).
-/

noncomputable section

open scoped Matrix ComplexConjugate

set_option autoImplicit false

namespace Langlands.Archimedean.HolomorphicJets

open MvPolynomial Langlands.GeneralLinear Langlands.Archimedean.NoncompactPicture
open Langlands.Archimedean.MomentSymbols Langlands.Archimedean.RealPolynomialFunctions
open Langlands.Archimedean.AdjacentGrowth Langlands.Archimedean.LevelFunctions
open Langlands.Archimedean.ComplexDuality

set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

/-- The columns `{k} ∪ {m+1, …, n-1}` (in the place of `m`, the column `k`). -/
def selCol (m k : Fin n) : Matrix (Fin n) (Tail n m) ℂ :=
  Matrix.of fun j i => if (i : Fin n) = m then (if j = k then 1 else 0)
    else (if j = (i : Fin n) then 1 else 0)

theorem nbMat_apply_of_lt {v : Lw n → ℂ} {a b : Fin n} (h : a < b) : nbMat v a b = 0 := by
  simp only [nbMat, lowMat, Matrix.add_apply, Matrix.one_apply_ne (ne_of_lt h), Matrix.of_apply,
    zero_add]
  rw [dite_eq_right (not_lt.2 h.le)]

theorem nbMat_apply_self (v : Lw n → ℂ) (a : Fin n) : nbMat v a a = 1 := by
  simp [nbMat, lowMat]

theorem tailRows_mul_selCol_apply (m k : Fin n) (y : Matrix (Fin n) (Fin n) ℂ)
    (i i' : Tail n m) :
    (tailRows (m : ℕ) y * selCol m k) i i' = if (i' : Fin n) = m then y i k else y i i' := by
  classical
  simp only [Matrix.mul_apply, tailRows, selCol, Matrix.of_apply]
  split_ifs
  · simp [Finset.sum_ite_eq']
  · simp [Finset.sum_ite_eq']

/-- **The selected determinant is the entry `(m, k)`.** -/
theorem levelDet_selCol (m k : Fin n) (_hk : k ≤ m) (v : Lw n → ℂ) :
    levelDet m (selCol m k) (nbMat v) = nbMat v m k := by
  classical
  have hm : (m : ℕ) ≤ ((m : Fin n) : ℕ) := le_rfl
  rw [levelDet, Matrix.det_of_isLowerTriangular]
  · rw [Finset.prod_eq_single (⟨m, hm⟩ : Tail n m)]
    · simp only [tailRows_mul_selCol_apply, ite_true]
    · intro i _ hi
      have hne : (i : Fin n) ≠ m := fun h => hi (Subtype.ext h)
      simp only [tailRows_mul_selCol_apply, hne, ite_false, nbMat_apply_self]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro i i' hii'
    have hlt : (i : Fin n) < (i' : Fin n) := hii'
    have hne : (i' : Fin n) ≠ m := by
      intro h
      have h1 := i.2
      have h2 : (i : ℕ) < (i' : ℕ) := hlt
      rw [h] at h2
      omega
    simp only [tailRows_mul_selCol_apply, hne, ite_false, nbMat_apply_of_lt hlt]

/-! ## The test functions -/

variable (γ : Lw n → ℕ)

/-- The exponents in the row `m`. -/
def gammaRow (m k : Fin n) : ℕ := if hk : k < m then γ ⟨(m, k), hk⟩ else 0

/-- The number of extra factors at the level `m`. -/
def jRow (m : Fin n) : ℕ := ∑ k, gammaRow γ m k

/-- The same, indexed by `ℕ`. -/
def jExt (m : ℕ) : ℕ := if hm : m < n then jRow γ ⟨m, hm⟩ else 0

theorem jExt_val (m : Fin n) : jExt γ m = jRow γ m := by
  rw [jExt, dite_eq_left m.2]

/-- The column labels of the extra factors. -/
def label (m : Fin n) (r : Fin (jRow γ m)) : Fin n :=
  ((finSigmaFinEquiv (n := gammaRow γ m)).symm r).1

theorem label_le (m : Fin n) (r : Fin (jRow γ m)) : label γ m r ≤ m := by
  have h := ((finSigmaFinEquiv (n := gammaRow γ m)).symm r).2
  by_contra hlt
  have h0 : gammaRow γ m ((finSigmaFinEquiv (n := gammaRow γ m)).symm r).1 = 0 := by
    rw [gammaRow, dite_eq_right]
    intro hk; exact hlt hk.le
  rw [h0] at h
  exact Fin.elim0 h

theorem prod_label {M : Type*} [CommMonoid M] (m : Fin n) (f : Fin n → M) :
    ∏ r : Fin (jRow γ m), f (label γ m r) = ∏ k, f k ^ gammaRow γ m k := by
  calc ∏ r : Fin (jRow γ m), f (label γ m r)
      = ∏ x : (Σ k, Fin (gammaRow γ m k)), f x.1 :=
        (Fintype.prod_equiv (finSigmaFinEquiv (n := gammaRow γ m)) (fun x => f x.1) _
          (fun x => by simp [label])).symm
    _ = ∏ k, f k ^ gammaRow γ m k := by
        rw [Fintype.prod_sigma]
        refine Finset.prod_congr rfl fun k _ => ?_
        simp

variable (h b : ℕ → ℕ) (dτ : ℕ → ℂ)

/-- The level matrices of the test function. -/
def testMat : LevelMatrices n (fun m => h m + jExt γ m) (fun m => b m + jExt γ m) :=
  fun m => (fun j => Fin.addCases (m := h m) (n := jRow γ m) (fun _ => selCol m m)
    (fun r => selCol m (label γ m r))
    (Fin.cast (show h m + jExt γ m = h m + jRow γ m by rw [jExt_val]) j), fun _ => selCol m m)

/-- **The test function.** -/
def testFun : Langlands.GeneralLinear n ℂ → ℂ :=
  levelProduct (fun m => h m + jExt γ m) (fun m => b m + jExt γ m) dτ (testMat γ h b)

theorem detPart_testMat (m : Fin n) (v : Lw n → ℂ) :
    detPart (fun m => h m + jExt γ m) (fun m => b m + jExt γ m) m (testMat γ h b m) (nbMat v) =
      ∏ k, nbMat v m k ^ gammaRow γ m k := by
  have h1 : levelDet m (selCol m m) (nbMat v) = 1 := by
    rw [levelDet_selCol m m le_rfl, nbMat_apply_self]
  have e : h m + jExt γ m = h m + jRow γ m := by rw [jExt_val]
  have hA : ∏ j : Fin (b m + jExt γ m), conj (levelDet m ((testMat γ h b m).2 j) (nbMat v)) = 1 :=
    Finset.prod_eq_one fun j _ => by
      show conj (levelDet m (selCol m m) (nbMat v)) = 1
      rw [h1, map_one]
  have hH : ∏ j : Fin (h m + jExt γ m), levelDet m ((testMat γ h b m).1 j) (nbMat v) =
      ∏ k, nbMat v m k ^ gammaRow γ m k := by
    refine (Fintype.prod_equiv (finCongr e) (fun j => levelDet m ((testMat γ h b m).1 j)
        (nbMat v)) (fun j => levelDet m (Fin.addCases (m := h m)
      (n := jRow γ m) (fun _ => selCol m m) (fun r => selCol m (label γ m r)) j) (nbMat v))
      (fun j => by rw [finCongr_apply]; rfl)).trans ?_
    rw [Fin.prod_univ_add]
    simp only [Fin.addCases_left, Fin.addCases_right]
    rw [Finset.prod_eq_one (fun j _ => h1), one_mul, ← prod_label γ m (fun k => nbMat v m k)]
    exact Finset.prod_congr rfl fun r _ => levelDet_selCol m _ (label_le γ m r) v
  rw [detPart, hH, hA, mul_one]

theorem gramExp_test (m : Fin n) :
    gramExp (fun m => h m + jExt γ m) (fun m => b m + jExt γ m) dτ m =
      gramExp h b dτ m - jRow γ m := by
  simp only [gramExp, jExt_val]
  push_cast
  ring

/-- **The test function on the lower unipotent group.** -/
theorem testFun_nbUnit (v : Lw n → ℂ) :
    testFun γ h b dτ (nbUnit v) =
      (∏ m, gramWeight m v ^ (gramExp h b dτ m - jRow γ m)) *
        ∏ m, ∏ k, nbMat v m k ^ gammaRow γ m k := by
  rw [testFun, levelProduct_nbUnit]
  simp only [gramExp_test, detPart_testMat]

/-- The polynomial `∏_m ∏_k (nbH)_{m k}^{γ_{m k}}`. -/
def testPoly : Hol n := ∏ m, ∏ k, nbH m k ^ gammaRow γ m k

theorem eval_testPoly (v : Lw n → ℂ) : eval v (testPoly γ) = ∏ m, ∏ k, nbMat v m k ^ gammaRow γ m k := by
  simp only [testPoly, map_prod, map_pow]
  refine Finset.prod_congr rfl fun m _ => Finset.prod_congr rfl fun k _ => ?_
  rw [← nbH_map_eval v]; rfl

theorem prod_lw {M : Type*} [CommMonoid M] (f : Lw n → M) :
    ∏ p, f p = ∏ i : Fin n, ∏ j : Fin n, if h : j < i then f ⟨(i, j), h⟩ else 1 := by
  classical
  rw [← Fintype.prod_prod_type', ← Fintype.prod_subtype_mul_prod_subtype (fun x : Fin n × Fin n =>
    x.2 < x.1)]
  rw [Finset.prod_eq_one (fun (y : {x : Fin n × Fin n // ¬ x.2 < x.1}) _ => dite_eq_right y.2),
    mul_one]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [dite_eq_left p.2]

theorem testPoly_eq : testPoly γ = ∏ p, X p ^ γ p := by
  rw [prod_lw, testPoly]
  refine Finset.prod_congr rfl fun m _ => Finset.prod_congr rfl fun k _ => ?_
  by_cases hk : k < m
  · rw [dite_eq_left hk, gammaRow, dite_eq_left hk, nbH_apply, ite_eq_right (ne_of_gt hk),
      dite_eq_left hk, zero_add]
  · rw [dite_eq_right hk, gammaRow, dite_eq_right hk, pow_zero]

/-- **The jet of the test function.** -/
theorem hasJet_testFun : HasJet (gramExp h b dτ) (testFun γ h b dτ) (ιP (testPoly γ)) := by
  classical
  set N := ∑ m, jRow γ m
  have hjN : ∀ m, jRow γ m ≤ N := fun m =>
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ m)
  refine ⟨N, (∏ m, gramF m ^ (N - jRow γ m)) * holIncl (testPoly γ), fun v => ?_, ?_⟩
  · have e1 : evalC (∏ m, gramF m ^ (N - jRow γ m)) v =
        ∏ m, AdjacentGrowth.gramWeight m v ^ (N - jRow γ m) := by
      rw [← evalAt_apply, map_prod]
      simp only [map_pow, evalAt_apply, evalC_gramF]
    have e2 : evalC (holIncl (testPoly γ)) v = ∏ m, ∏ k, nbMat v m k ^ gammaRow γ m k :=
      (evalC_holIncl _ _).trans (eval_testPoly γ v)
    simp only [testFun_nbUnit, evalC_mul, e1, e2]
    generalize ∏ m, ∏ k, nbMat v m k ^ gammaRow γ m k = A
    have key : ∀ m, AdjacentGrowth.gramWeight m v ^ (gramExp h b dτ m - jRow γ m) *
        AdjacentGrowth.gramWeight m v ^ N = AdjacentGrowth.gramWeight m v ^ gramExp h b dτ m *
          AdjacentGrowth.gramWeight m v ^ (N - jRow γ m) := by
      intro m
      have hG := (isPosReal_gramWeight m).ne_zero v
      have hN : N = jRow γ m + (N - jRow γ m) := by have := hjN m; omega
      rw [Complex.cpow_sub _ _ hG, Complex.cpow_natCast]
      conv_lhs => rw [hN, pow_add]
      field_simp
    rw [← Finset.prod_pow]
    calc (∏ m, AdjacentGrowth.gramWeight m v ^ (gramExp h b dτ m - jRow γ m)) * A *
          ∏ m, AdjacentGrowth.gramWeight m v ^ N
        = (∏ m, (AdjacentGrowth.gramWeight m v ^ (gramExp h b dτ m - jRow γ m) *
            AdjacentGrowth.gramWeight m v ^ N)) * A := by rw [Finset.prod_mul_distrib]; ring
      _ = _ := by
        simp only [key, Finset.prod_mul_distrib]
        ring
  · rw [map_mul, map_prod, holPart_holIncl]
    simp only [map_pow, holPart_gramF, one_pow, Finset.prod_const_one, one_mul]

/-- **The test function is a `U(n)`-finite principal-series function** when the level data
telescope to `χ`. -/
theorem testFun_mem_kFiniteFunctions {χ : ℕ → ℂˣ → ℂ} (l : ℕ → ℤ) (t : ℕ → ℂ)
    (hχ : ∀ k z, χ k z = phase z ^ l k * ((‖(z : ℂ)‖ : ℂ)) ^ (2 * t k))
    (hl : ∀ k : Fin n, ∑ m ∈ Finset.univ.filter (fun m : Fin n => m.val ≤ k.val),
      ((h m : ℤ) - b m) = l k)
    (hτ : ∀ k : Fin n, ∑ m ∈ Finset.univ.filter (fun m : Fin n => m.val ≤ k.val), dτ m =
      t k + ((n : ℂ) - 1) / 2 - (k : ℕ)) :
    testFun γ h b dτ ∈ kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n) := by
  refine levelSpan_le_kFiniteFunctions _ _ dτ l t hχ (fun k => ?_) hτ
    (Submodule.subset_span ⟨testMat γ h b, rfl⟩)
  rw [← hl k]
  refine Finset.sum_congr rfl fun m _ => ?_
  push_cast
  ring

end Langlands.Archimedean.HolomorphicJets
