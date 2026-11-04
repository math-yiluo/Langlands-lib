import Langlands.GroupScheme.Unipotent.OneDimensional.Additive
import Langlands.GroupScheme.Unipotent.OneDimensional.Invariant
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Algebraic relations between primitive elements are additive -/

noncomputable section

open Polynomial TensorProduct
open Algebra.TensorProduct (includeLeft includeRight)

namespace Langlands.GroupScheme.Unipotent.OneDimensional

section Coeff

variable {k : Type*} [Field k]

/-- The coefficient of `X^a Y^b` in `c = ∑ cⱼ(X) Yʲ ∈ k[X][Y]`. -/
abbrev coeff2 (c : k[X][X]) (a b : ℕ) : k :=
  (c.coeff b).coeff a

theorem ext2 {c d : k[X][X]} (h : ∀ a b, coeff2 c a b = coeff2 d a b) : c = d :=
  Polynomial.ext fun b => Polynomial.ext fun a => h a b

@[simp] theorem coeff2_zero (a b : ℕ) : coeff2 (0 : k[X][X]) a b = 0 := by
  simp [coeff2]

theorem coeff2_C (f : k[X]) (a b : ℕ) :
    coeff2 (C f : k[X][X]) a b = if b = 0 then f.coeff a else 0 := by
  by_cases hb : b = 0 <;> simp [coeff2, coeff_C, hb]

theorem coeff2_map_C (f : k[X]) (a b : ℕ) :
    coeff2 (f.map C) a b = if a = 0 then f.coeff b else 0 := by
  by_cases ha : a = 0 <;> simp [coeff2, coeff_map, coeff_C, ha]

@[simp] theorem coeff2_add (c d : k[X][X]) (a b : ℕ) :
    coeff2 (c + d) a b = coeff2 c a b + coeff2 d a b := by
  simp [coeff2]

@[simp] theorem coeff2_sub (c d : k[X][X]) (a b : ℕ) :
    coeff2 (c - d) a b = coeff2 c a b - coeff2 d a b := by
  simp [coeff2]

@[simp] theorem coeff2_smul (r : k) (c : k[X][X]) (a b : ℕ) :
    coeff2 (r • c) a b = r * coeff2 c a b := by
  simp [coeff2]

theorem coeff2_C_C (r : k) (a b : ℕ) :
    coeff2 (C (C r) : k[X][X]) a b = if a = 0 ∧ b = 0 then r else 0 := by
  by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> simp [coeff2, coeff_C, ha, hb]

/-- All exponents of `c` are at most `D`. -/
def Bdd (D : ℕ) (c : k[X][X]) : Prop :=
  ∀ a b, coeff2 c a b ≠ 0 → a ≤ D ∧ b ≤ D

theorem exists_bdd (c : k[X][X]) : ∃ D, Bdd D c := by
  refine ⟨c.natDegree + ∑ b ∈ Finset.range (c.natDegree + 1), (c.coeff b).natDegree, ?_⟩
  intro a b hab
  have hb0 : c.coeff b ≠ 0 := fun h => hab (by rw [coeff2, h, Polynomial.coeff_zero])
  have hb : b ≤ c.natDegree := le_natDegree_of_ne_zero hb0
  have ha : a ≤ (c.coeff b).natDegree := le_natDegree_of_ne_zero hab
  have hs : (c.coeff b).natDegree ≤
      ∑ b ∈ Finset.range (c.natDegree + 1), (c.coeff b).natDegree :=
    Finset.single_le_sum (f := fun b => (c.coeff b).natDegree) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hb))
  omega

theorem Bdd.natDegree_le {D : ℕ} {c : k[X][X]} (hc : Bdd D c) : c.natDegree ≤ D := by
  rw [natDegree_le_iff_coeff_eq_zero]
  intro N hN
  by_contra h
  obtain ⟨a, ha⟩ : ∃ a, (c.coeff N).coeff a ≠ 0 := by
    by_contra h'
    push Not at h'
    exact h (Polynomial.ext fun a => by rw [h' a, Polynomial.coeff_zero])
  have := (hc a N ha).2
  exact absurd hN (not_lt.2 (by exact_mod_cast this))

theorem coeff2_swap (c : k[X][X]) (a b : ℕ) : coeff2 (Bivariate.swap c) a b = coeff2 c b a :=
  coeff_coeff_swap c a b

theorem Bdd.swap {D : ℕ} {c : k[X][X]} (hc : Bdd D c) : Bdd D (Bivariate.swap c) := by
  intro a b hab
  rw [coeff2_swap] at hab
  exact (hc b a hab).symm

theorem coeff2_hasseDeriv (j : ℕ) (c : k[X][X]) (a b : ℕ) :
    coeff2 (hasseDeriv j c) a b = ((b + j).choose j : k) * coeff2 c a (b + j) := by
  rw [coeff2, hasseDeriv_coeff, coeff_natCast_mul]

theorem Bdd.hasseDeriv {D : ℕ} {c : k[X][X]} (hc : Bdd D c) (j : ℕ) : Bdd D (hasseDeriv j c) := by
  intro a b hab
  rw [coeff2_hasseDeriv] at hab
  have := hc a (b + j) (right_ne_zero_of_mul hab)
  omega

/-- A polynomial with prescribed coefficients and exponents at most `D`. -/
def mk2 (D : ℕ) (h : ℕ → ℕ → k) : k[X][X] :=
  ∑ j ∈ Finset.range (D + 1), ∑ i ∈ Finset.range (D + 1), monomial j (monomial i (h i j))

theorem coeff2_mk2 (D : ℕ) (h : ℕ → ℕ → k) (hh : ∀ a b, ¬ (a ≤ D ∧ b ≤ D) → h a b = 0)
    (a b : ℕ) : coeff2 (mk2 D h) a b = h a b := by
  simp only [coeff2, mk2, finsetSum_coeff, coeff_coeff_monomial_monomial]
  rw [Finset.sum_eq_single b, Finset.sum_eq_single a]
  · simp
  · intro i _ hi
    simp [hi]
  · intro ha
    by_cases hb : b ≤ D
    · simp only [Finset.mem_range, not_lt] at ha
      simp only [true_and, ite_eq_right_iff]
      intro h'
      exact hh a b (by omega)
    · simp only [true_and, ite_eq_right_iff]
      intro _
      exact hh a b (by omega)
  · intro j _ hj
    apply Finset.sum_eq_zero
    intro i _
    simp [hj]
  · intro hb
    simp only [Finset.mem_range, not_lt] at hb
    apply Finset.sum_eq_zero
    intro i _
    simp only [true_and, ite_eq_right_iff]
    rintro rfl
    exact hh i b (by omega)

theorem ev2_mk2 {R : Type*} [CommRing R] [Algebra k R] (u v : R) (D : ℕ) (h : ℕ → ℕ → k) :
    ev2 u v (mk2 D h) =
      ∑ j ∈ Finset.range (D + 1), ∑ i ∈ Finset.range (D + 1), h i j • (u ^ i * v ^ j) := by
  simp only [mk2, map_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [ev2_apply, eval₂_monomial, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_monomial,
    Algebra.smul_def, mul_assoc]

theorem ev2_map_C {R : Type*} [CommRing R] [Algebra k R] (u v : R) (f : k[X]) :
    ev2 u v (f.map C) = aeval v f := by
  rw [ev2_apply, eval₂_map, aeval_def]
  congr 1
  ext r
  simp

theorem ev2_zero_zero (c : k[X][X]) : ev2 (0 : k) 0 c = coeff2 c 0 0 := by
  rw [ev2_apply, eval₂_at_zero]
  exact (coeff_zero_eq_aeval_zero (c.coeff 0)).symm

end Coeff

section Taylor

variable {k : Type*} [Field k]

/-- Taylor's formula `G(x + h) = ∑ⱼ (Dʲ G)(x) hʲ` with Hasse derivatives. -/
theorem eval_add_eq_sum {S : Type*} [CommRing S] (G : S[X]) (x h : S) {N : ℕ}
    (hN : G.natDegree ≤ N) :
    G.eval (x + h) = ∑ j ∈ Finset.range (N + 1), (hasseDeriv j G).eval x * h ^ j := by
  rw [add_comm, ← taylor_eval, eval_eq_sum_range' (n := N + 1)
    (by rw [natDegree_taylor]; omega)]
  simp only [taylor_coeff]

/-- Taylor's formula in the outer variable. -/
theorem ev2_add_right {R : Type*} [CommRing R] [Algebra k R] (u v' v : R) {N : ℕ}
    {c : k[X][X]} (hN : c.natDegree ≤ N) :
    ev2 u (v' + v) c = ∑ j ∈ Finset.range (N + 1), ev2 u v' (hasseDeriv j c) * v ^ j := by
  rw [ev2_apply, eval₂_eq_eval_map, eval_add_eq_sum _ _ _ (natDegree_map_le.trans hN)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hasseDeriv_map, eval_map, ← ev2_apply]

/-- Taylor's formula in the inner variable. -/
theorem ev2_add_left {R : Type*} [CommRing R] [Algebra k R] (u' u v : R) {N : ℕ}
    {c : k[X][X]} (hN : (Bivariate.swap c).natDegree ≤ N) :
    ev2 (u' + u) v c = ∑ i ∈ Finset.range (N + 1),
      ev2 u' v (Bivariate.swap (hasseDeriv i (Bivariate.swap c))) * u ^ i := by
  rw [← ev2_swap, ev2_add_right _ _ _ hN]
  simp only [ev2_swap]

/-- The Taylor coefficient `H_{ij}` of `c`, so that
`c(u' + u, v' + v) = ∑ H_{ij}(u', v') uⁱ vʲ`. -/
def taylorCoeff (c : k[X][X]) (i j : ℕ) : k[X][X] :=
  Bivariate.swap (hasseDeriv i (Bivariate.swap (hasseDeriv j c)))

theorem coeff2_taylorCoeff (c : k[X][X]) (i j a b : ℕ) :
    coeff2 (taylorCoeff c i j) a b =
      ((a + i).choose i : k) * (((b + j).choose j : k) * coeff2 c (a + i) (b + j)) := by
  rw [taylorCoeff, coeff2_swap, coeff2, hasseDeriv_coeff, coeff_natCast_mul, ← coeff2,
    coeff2_swap, coeff2_hasseDeriv]

/-- Two-variable Taylor formula. -/
theorem ev2_add_add {R : Type*} [CommRing R] [Algebra k R] {D : ℕ} {c : k[X][X]}
    (hc : Bdd D c) (u' u v' v : R) :
    ev2 (u' + u) (v' + v) c = ∑ j ∈ Finset.range (D + 1), ∑ i ∈ Finset.range (D + 1),
      ev2 u' v' (taylorCoeff c i j) * u ^ i * v ^ j := by
  rw [ev2_add_right _ _ _ hc.natDegree_le]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ev2_add_left _ _ _ ((hc.hasseDeriv j).swap.natDegree_le), Finset.sum_mul]
  rfl

theorem taylorCoeff_eq_C_C (c : k[X][X]) (i j : ℕ)
    (h : ∀ a b, 0 < a + b → coeff2 c (a + i) (b + j) = 0) :
    taylorCoeff c i j = C (C (coeff2 c i j)) := by
  apply ext2
  intro a b
  rw [coeff2_taylorCoeff, coeff2_C_C]
  by_cases hab : a = 0 ∧ b = 0
  · obtain ⟨rfl, rfl⟩ := hab
    simp
  · rw [ite_eq_right hab, h a b (by omega), mul_zero, mul_zero]

end Taylor

section Minimal

variable {k : Type*} [Field k]

/-- All nonzero coefficients `X^a Y^b` of `g` satisfy `(b, a) < (n, m)` lexicographically. -/
def Below (n m : ℕ) (g : k[X][X]) : Prop :=
  ∀ a b, coeff2 g a b ≠ 0 → b < n ∨ (b = n ∧ a < m)

theorem coeff2_natDegree_ne_zero {g : k[X][X]} (hg : g ≠ 0) :
    coeff2 g g.leadingCoeff.natDegree g.natDegree ≠ 0 := by
  rw [coeff2, coeff_natDegree, coeff_natDegree, Ne, leadingCoeff_eq_zero, leadingCoeff_eq_zero]
  exact hg

theorem support_le (c : k[X][X]) (a b : ℕ) (h : coeff2 c a b ≠ 0) :
    b < c.natDegree ∨ (b = c.natDegree ∧ a ≤ c.leadingCoeff.natDegree) := by
  have hb0 : c.coeff b ≠ 0 := fun h' => h (by rw [coeff2, h', Polynomial.coeff_zero])
  rcases (le_natDegree_of_ne_zero hb0).lt_or_eq with hb | rfl
  · exact Or.inl hb
  · exact Or.inr ⟨rfl, le_natDegree_of_ne_zero h⟩

/-- A lexicographically minimal nonzero element of a nonempty set of polynomials. -/
theorem exists_minimal (P : k[X][X] → Prop) {c₀ : k[X][X]} (h₀ : c₀ ≠ 0) (hP₀ : P c₀) :
    ∃ c, c ≠ 0 ∧ P c ∧ ∀ g, P g → Below c.natDegree c.leadingCoeff.natDegree g → g = 0 := by
  classical
  have hex : ∃ n, ∃ c : k[X][X], c ≠ 0 ∧ P c ∧ c.natDegree = n := ⟨_, c₀, h₀, hP₀, rfl⟩
  have hex2 : ∃ m, ∃ c : k[X][X], c ≠ 0 ∧ P c ∧ c.natDegree = Nat.find hex ∧
      c.leadingCoeff.natDegree = m := by
    obtain ⟨c, hc, hPc, hn⟩ := Nat.find_spec hex
    exact ⟨_, c, hc, hPc, hn, rfl⟩
  obtain ⟨c, hc, hPc, hn, hm⟩ := Nat.find_spec hex2
  refine ⟨c, hc, hPc, fun g hPg hg => ?_⟩
  by_contra hg0
  rcases hg _ _ (coeff2_natDegree_ne_zero hg0) with h | ⟨h1, h2⟩
  · exact Nat.find_min hex (h.trans_eq hn) ⟨g, hg0, hPg, rfl⟩
  · exact Nat.find_min hex2 (h2.trans_eq hm) ⟨g, hg0, hPg, h1.trans hn, rfl⟩

end Minimal

section Additive

variable {k : Type*} [Field k]

theorem isAdditive_of_coeff (f : k[X]) (h0 : f.coeff 0 = 0)
    (h : ∀ a n, 0 < a → 0 < n → ((a + n).choose n : k) * f.coeff (a + n) = 0) :
    IsAdditive f := by
  show coboundary f = 0
  apply ext2
  intro a b
  simp only [coeff2, coeff_coboundary, coeff_sub, hasseDeriv_coeff, coeff_C,
    Polynomial.coeff_zero]
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp [h0]
    · simp [ha.ne']
  · rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp [hb.ne']
    · simp [hb.ne', ha.ne', h a b ha hb]

end Additive

section Bialgebra

variable {k B : Type*} [Field k] [CommRing B] [Bialgebra k B]

open Coalgebra

theorem comul_ev2 {y t : B} (hy : Bialgebra.IsPrimitiveElem k y)
    (ht : Bialgebra.IsPrimitiveElem k t) (c : k[X][X]) :
    comul (R := k) (ev2 y t c) = ev2 (1 ⊗ₜ y + y ⊗ₜ 1) (1 ⊗ₜ t + t ⊗ₜ 1) c := by
  have h := comp_ev2 (Bialgebra.comulAlgHom k B) y t c
  simp only [Bialgebra.comulAlgHom_apply, hy.comul_eq_tmul_add_tmul,
    ht.comul_eq_tmul_add_tmul] at h
  exact h

/-- The comultiplication of a polynomial in two primitive elements, expanded by Taylor's
formula. -/
theorem comul_ev2_eq_sum {y t : B} (hy : Bialgebra.IsPrimitiveElem k y)
    (ht : Bialgebra.IsPrimitiveElem k t) {D : ℕ} {c : k[X][X]} (hc : Bdd D c) :
    comul (R := k) (ev2 y t c) = ∑ j ∈ Finset.range (D + 1), ∑ i ∈ Finset.range (D + 1),
      (y ^ i * t ^ j) ⊗ₜ[k] ev2 y t (taylorCoeff c i j) := by
  rw [comul_ev2 hy ht, ev2_add_add hc]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [show ev2 ((1 : B) ⊗ₜ[k] y) (1 ⊗ₜ t) (taylorCoeff c i j) =
      (1 : B) ⊗ₜ[k] ev2 y t (taylorCoeff c i j) from
    (comp_ev2 (includeRight : B →ₐ[k] B ⊗[k] B) y t _).symm]
  simp only [Algebra.TensorProduct.tmul_pow, one_pow, Algebra.TensorProduct.tmul_mul_tmul,
    one_mul, mul_one]

/-- Contracting the expanded comultiplication of a relation gives a new relation. -/
theorem ev2_contract {y t : B} (hy : Bialgebra.IsPrimitiveElem k y)
    (ht : Bialgebra.IsPrimitiveElem k t) {D : ℕ} {c : k[X][X]} (hc : Bdd D c)
    (hrel : ev2 y t c = 0) (φ : Module.Dual k B) :
    ev2 y t (mk2 D fun i j => φ (ev2 y t (taylorCoeff c i j))) = 0 := by
  have h := congrArg (fun w => TensorProduct.rid k B (φ.lTensor B w)) (comul_ev2_eq_sum hy ht hc)
  simp only [hrel, map_zero, map_sum, LinearMap.lTensor_tmul, TensorProduct.rid_tmul] at h
  rw [ev2_mk2]
  exact h.symm

/-- **Relations between primitive elements are additive.** If two primitive elements `y, t`
satisfy a nonzero polynomial relation, then they satisfy a relation `α(y) + β(t) = 0` with
additive polynomials `α, β`, not both zero. -/
theorem exists_additive_relation {y t : B} (hy : Bialgebra.IsPrimitiveElem k y)
    (ht : Bialgebra.IsPrimitiveElem k t) {c₀ : k[X][X]} (hc₀ : c₀ ≠ 0)
    (hrel₀ : ev2 y t c₀ = 0) :
    ∃ α β : k[X], IsAdditive α ∧ IsAdditive β ∧ (α ≠ 0 ∨ β ≠ 0) ∧
      aeval y α + aeval t β = 0 := by
  classical
  obtain ⟨c, hc0, hrel, hmin⟩ := exists_minimal (fun g => ev2 y t g = 0) hc₀ hrel₀
  obtain ⟨D, hD⟩ := exists_bdd c
  set n := c.natDegree with hn
  set m := c.leadingCoeff.natDegree with hm
  -- The Taylor coefficients at or above the leading exponent are constant.
  have htop : ∀ a b, n ≤ b → (b = n → m ≤ a) →
      taylorCoeff c a b = C (C (coeff2 c a b)) := by
    intro a b hb ha
    apply taylorCoeff_eq_C_C
    intro a' b' hab
    by_contra hne
    rcases support_le c _ _ hne with h | ⟨h1, h2⟩
    · omega
    · have := ha (by omega)
      omega
  have hbox : ∀ a b, ¬ (a ≤ D ∧ b ≤ D) → taylorCoeff c a b = 0 := by
    intro a b hab
    apply ext2
    intro a' b'
    rw [coeff2_taylorCoeff, coeff2_zero]
    by_cases h : coeff2 c (a' + a) (b' + b) = 0
    · rw [h, mul_zero, mul_zero]
    · have := hD _ _ h
      omega
  -- Step 1: contracting with any functional reproduces the relation.
  have hφ : ∀ φ : Module.Dual k B, ∀ i j,
      φ (ev2 y t (taylorCoeff c i j)) = φ 1 * coeff2 c i j := by
    intro φ
    have hcoef : ∀ i j, coeff2 (mk2 D fun i j => φ (ev2 y t (taylorCoeff c i j))) i j =
        φ (ev2 y t (taylorCoeff c i j)) := by
      refine coeff2_mk2 D _ fun i j hij => ?_
      rw [hbox i j hij, map_zero, map_zero]
    have hrel' : ev2 y t ((mk2 D fun i j => φ (ev2 y t (taylorCoeff c i j))) - φ 1 • c) = 0 := by
      rw [map_sub, map_smul, ev2_contract hy ht hD hrel, hrel, smul_zero, sub_zero]
    have hbelow : Below n m ((mk2 D fun i j => φ (ev2 y t (taylorCoeff c i j))) - φ 1 • c) := by
      intro a b hab
      by_contra hcon
      apply hab
      rw [coeff2_sub, coeff2_smul, hcoef, htop a b (by omega) (by omega), ev2_C, aeval_C,
        Algebra.algebraMap_eq_smul_one, map_smul, smul_eq_mul, mul_comm, sub_self]
    have h0 := hmin _ hrel' hbelow
    intro i j
    have h2 := congrArg (fun g => coeff2 g i j) h0
    simp only [coeff2_sub, coeff2_smul, hcoef, coeff2_zero] at h2
    exact sub_eq_zero.mp h2
  -- Step 2: the Taylor coefficients evaluate to constants.
  have hH : ∀ i j, ev2 y t (taylorCoeff c i j) = algebraMap k B (coeff2 c i j) := by
    intro i j
    rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff k]
    intro φ
    rw [map_sub, hφ, Algebra.algebraMap_eq_smul_one, map_smul, smul_eq_mul, mul_comm, sub_self]
  -- Step 3: by minimality, the Taylor coefficients are constants.
  have hHc : ∀ i j, 0 < i + j → taylorCoeff c i j = C (C (coeff2 c i j)) := by
    intro i j hij
    rw [← sub_eq_zero]
    apply hmin
    · show ev2 y t (taylorCoeff c i j - C (C (coeff2 c i j))) = 0
      rw [map_sub, hH, ev2_C, aeval_C, sub_self]
    · intro a b hab
      rw [coeff2_sub, coeff2_taylorCoeff, coeff2_C_C] at hab
      by_cases h0 : a = 0 ∧ b = 0
      · obtain ⟨rfl, rfl⟩ := h0
        simp at hab
      · rw [ite_eq_right h0, sub_zero] at hab
        rcases support_le c _ _ (right_ne_zero_of_mul (right_ne_zero_of_mul hab)) with h | ⟨h1, h2⟩
        · omega
        · omega
  have hvan : ∀ i j a b, 0 < i + j → 0 < a + b →
      ((a + i).choose i : k) * (((b + j).choose j : k) * coeff2 c (a + i) (b + j)) = 0 := by
    intro i j a b hij hab
    have h := congrArg (fun g => coeff2 g a b) (hHc i j hij)
    simp only [coeff2_taylorCoeff, coeff2_C_C] at h
    rw [h, ite_eq_right (by omega)]
  -- Step 4: the constant term vanishes.
  have h00 : coeff2 c 0 0 = 0 := by
    have h := comp_ev2 (Bialgebra.counitAlgHom k B) y t c
    rw [hrel, map_zero, Bialgebra.counitAlgHom_apply, Bialgebra.counitAlgHom_apply,
      hy.counit_eq_zero, ht.counit_eq_zero, ev2_zero_zero] at h
    exact h.symm
  -- Step 5: `c = α(X) + β(Y)` with `α, β` additive.
  let α : k[X] := c.coeff 0
  let β : k[X] := c.map constantCoeff
  have hα : ∀ a, α.coeff a = coeff2 c a 0 := fun a => rfl
  have hβ : ∀ b, β.coeff b = coeff2 c 0 b := fun b => by
    simp [β, coeff2, coeff_map, coeff_zero_eq_eval_zero]
  have hmixed : ∀ a b, 0 < a → 0 < b → coeff2 c a b = 0 := by
    intro a b ha hb
    have := hvan a 0 0 b (by omega) (by omega)
    simpa using this
  have hdec : c = C α + β.map C := by
    apply ext2
    intro a b
    rw [coeff2_add, coeff2_C, coeff2_map_C, hβ]
    rcases Nat.eq_zero_or_pos b with rfl | hb <;> rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp [hα, h00]
    · simp [ha.ne', hα]
    · simp [hb.ne']
    · simp [ha.ne', hb.ne', hmixed a b ha hb]
  have hαadd : IsAdditive α := by
    refine isAdditive_of_coeff α (by rw [hα]; exact h00) fun a q ha hq => ?_
    have := hvan q 0 a 0 (by omega) (by omega)
    simpa [hα] using this
  have hβadd : IsAdditive β := by
    refine isAdditive_of_coeff β (by rw [hβ]; exact h00) fun a q ha hq => ?_
    have := hvan 0 q 0 a (by omega) (by omega)
    simpa [hβ] using this
  refine ⟨α, β, hαadd, hβadd, ?_, ?_⟩
  · by_contra h
    push Not at h
    apply hc0
    rw [hdec, h.1, h.2]
    simp
  · have h := hrel
    rw [hdec, map_add, ev2_C, ev2_map_C] at h
    exact h

end Bialgebra

end Langlands.GroupScheme.Unipotent.OneDimensional
