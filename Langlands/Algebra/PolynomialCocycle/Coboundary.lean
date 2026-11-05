import Langlands.Algebra.PolynomialCocycle.Homogeneous

/-!
# Symmetric polynomial 2-cocycles are coboundaries

A bivariate polynomial is an iterated polynomial `c : k[X][X]`, whose inner variable is the
first argument; `aevalAeval x y c` evaluates it at `(x, y)`.
-/

noncomputable section

universe u

namespace Langlands.Algebra.PolynomialCocycle

open Polynomial Polynomial.Bivariate Finset

section Evaluation

variable {R : Type*} [CommRing R]

/-- The Taylor expansion at the variable of a polynomial with constant coefficients. -/
theorem coeff_taylor_X_map_C (p : R[X]) (n : ℕ) :
    (taylor (X : R[X]) (p.map C)).coeff n = hasseDeriv n p := by
  rw [taylor_coeff, hasseDeriv_map, eval_map, eval₂_C_X]

/-- Substituting `X + C X` into a polynomial is a Taylor expansion. -/
theorem aeval_X_add_C_X (p : R[X]) :
    aeval (X + C X : R[X][X]) p = taylor (X : R[X]) (p.map C) := by
  rw [taylor_apply, comp, eval₂_map, aeval_def]
  rfl

/-- The coefficients of `swap c`. -/
theorem coeff_coeff_swap (c : R[X][X]) (i j : ℕ) :
    ((swap c).coeff j).coeff i = (c.coeff i).coeff j := by
  induction c using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, coeff_add, hp, hq]
  | monomial n a =>
    induction a using Polynomial.induction_on' with
    | add a b ha hb => simp only [map_add, coeff_add, ha, hb]
    | monomial m r =>
      rw [swap_monomial_monomial]
      simp only [coeff_monomial]
      split_ifs <;> simp_all [coeff_monomial]

variable {A : Type*} [CommSemiring A] [Algebra R A]

/-- An algebra map out of `R[X][X]` is evaluation at its values on the two variables. -/
theorem aevalAeval_eq (f : R[X][X] →ₐ[R] A) : aevalAeval (f (C X)) (f X) = f :=
  (aevalAevalEquiv R A).apply_symm_apply f

theorem aevalAeval_C_X_X : aevalAeval (C X : R[X][X]) X = AlgHom.id R R[X][X] := by
  simpa using aevalAeval_eq (AlgHom.id R R[X][X])

/-- Evaluation at `(C (C X), C X)` in `R[X][X][X]` is the constant embedding. -/
theorem aevalAeval_term₁ (c : R[X][X]) :
    aevalAeval (C (C X) : R[X][X][X]) (C X) c = C c := by
  have h := aevalAeval_eq (A := R[X][X][X]) (CAlgHom (R := R) (A := R[X][X]))
  simp only [CAlgHom_apply] at h
  rw [h, CAlgHom_apply]

/-- Evaluation at `(C (C X) + C X, X)` in `R[X][X][X]`. -/
theorem aevalAeval_term₂ (c : R[X][X]) :
    aevalAeval (C (C X) + C X : R[X][X][X]) X c =
      c.map (aeval (X + C X : R[X][X]) : R[X] →ₐ[R] R[X][X]).toRingHom := by
  have h := aevalAeval_eq (A := R[X][X][X])
    (mapAlgHom (aeval (X + C X : R[X][X]) : R[X] →ₐ[R] R[X][X]))
  rw [coe_mapAlgHom, map_C, map_X] at h
  simp only [RingHom.coe_coe, aeval_X, C_add, add_comm (C X)] at h
  rw [h, coe_mapAlgHom]
  rfl

/-- Evaluation at `(C X, X)` in `R[X][X][X]`. -/
theorem aevalAeval_term₃ (c : R[X][X]) :
    aevalAeval (C X : R[X][X][X]) X c =
      c.map (aeval (X : R[X][X]) : R[X] →ₐ[R] R[X][X]).toRingHom := by
  have h := aevalAeval_eq (A := R[X][X][X])
    (mapAlgHom (aeval (X : R[X][X]) : R[X] →ₐ[R] R[X][X]))
  rw [coe_mapAlgHom, map_C, map_X] at h
  simp only [RingHom.coe_coe, aeval_X] at h
  rw [h, coe_mapAlgHom]
  rfl

/-- Evaluation at `(C (C X), C X + X)` in `R[X][X][X]` is a Taylor expansion. -/
theorem aevalAeval_term₄ (c : R[X][X]) :
    aevalAeval (C (C X) : R[X][X][X]) (C X + X) c = taylor (X : R[X][X]) (c.map C) := by
  have h := aevalAeval_eq (A := R[X][X][X]) (((taylorAlgHom (X : R[X][X])).restrictScalars R).comp
    (mapAlgHom (CAlgHom (R := R) (A := R[X]))))
  simp only [AlgHom.comp_apply, AlgHom.coe_restrictScalars', coe_mapAlgHom, map_C, map_X,
    taylorAlgHom_apply, taylor_C, taylor_X, add_comm X] at h
  exact (DFunLike.congr_fun h c).trans rfl

/-- Coefficients of the evaluation at `(C r * X, X)`, a weighted diagonal. -/
theorem coeff_aevalAeval_C_mul_X_X (c : R[X][X]) (r : R) (n : ℕ) :
    (aevalAeval (C r * X : R[X]) X c).coeff n =
      ∑ l ∈ range (n + 1), (c.coeff (n - l)).coeff l * r ^ l := by
  induction c using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, coeff_add, hp, hq, add_mul, sum_add_distrib]
  | monomial j a =>
    rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow, aevalAeval_C, aevalAeval_Y,
      ← comp_eq_aeval, coeff_mul_X_pow']
    simp only [coeff_C_mul_X_pow]
    split_ifs with hj
    · rw [comp_C_mul_X_coeff, sum_eq_single_of_mem (n - j) (mem_range.2 (by omega))]
      · rw [ite_eq_left (by omega)]
      · intro l hl hlj
        rw [ite_eq_right (by rw [mem_range] at hl; omega), coeff_zero, zero_mul]
    · refine (sum_eq_zero fun l hl => ?_).symm
      rw [ite_eq_right (by rw [mem_range] at hl; omega), coeff_zero, zero_mul]

/-- Coefficients of the constant embedding `R[X][X] → R[X][X][X]`. -/
theorem coeff_coeff_coeff_C (c : R[X][X]) (a b e : ℕ) :
    ((((C c : R[X][X][X]).coeff e).coeff b).coeff a) =
      if e = 0 then (c.coeff b).coeff a else 0 := by
  rw [coeff_C]
  split_ifs <;> simp

/-- Coefficients of `c (u + v, w)`. -/
theorem coeff_coeff_coeff_term₂ (c : R[X][X]) (a b e : ℕ) :
    ((((c.map (aeval (X + C X : R[X][X]) : R[X] →ₐ[R] R[X][X]).toRingHom).coeff e).coeff b).coeff
      a) = ((a + b).choose b : R) * (c.coeff e).coeff (a + b) := by
  rw [coeff_map, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_X_add_C_X, coeff_taylor_X_map_C,
    hasseDeriv_coeff]

/-- Coefficients of `c (v, w)`. -/
theorem coeff_coeff_coeff_term₃ (c : R[X][X]) (a b e : ℕ) :
    ((((c.map (aeval (X : R[X][X]) : R[X] →ₐ[R] R[X][X]).toRingHom).coeff e).coeff b).coeff a) =
      if a = 0 then (c.coeff e).coeff b else 0 := by
  rw [coeff_map, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    show aeval (X : R[X][X]) (c.coeff e) = (c.coeff e).map C from rfl, coeff_map, coeff_C]

/-- Coefficients of `c (u, v + w)`. -/
theorem coeff_coeff_coeff_term₄ (c : R[X][X]) (a b e : ℕ) :
    ((((taylor (X : R[X][X]) (c.map C)).coeff e).coeff b).coeff a) =
      ((b + e).choose e : R) * (c.coeff (b + e)).coeff a := by
  rw [coeff_taylor_X_map_C, hasseDeriv_coeff, coeff_natCast_mul]

end Evaluation

section Coboundary

variable {k : Type u} [Field k]

/-- The cocycle identity, read off coefficientwise from the universal point. -/
theorem coeff_rel (c : k[X][X])
    (hcoc : ∀ (R : Type u) [CommRing R] [Algebra k R] (x y z : R),
      aevalAeval x y c + aevalAeval (x + y) z c = aevalAeval y z c + aevalAeval x (y + z) c)
    (a b e : ℕ) :
    (if e = 0 then (c.coeff b).coeff a else 0) +
        ((a + b).choose b : k) * (c.coeff e).coeff (a + b) =
      (if a = 0 then (c.coeff e).coeff b else 0) +
        ((b + e).choose e : k) * (c.coeff (b + e)).coeff a := by
  have h := hcoc k[X][X][X] (C (C X)) (C X) X
  rw [aevalAeval_term₁, aevalAeval_term₂, aevalAeval_term₃, aevalAeval_term₄] at h
  have h' := congrArg (fun q : k[X][X][X] => ((q.coeff e).coeff b).coeff a) h
  simp only [coeff_add] at h'
  rwa [coeff_coeff_coeff_C, coeff_coeff_coeff_term₂, coeff_coeff_coeff_term₃,
    coeff_coeff_coeff_term₄] at h'

/-- Symmetry, read off coefficientwise. -/
theorem coeff_symm (c : k[X][X])
    (hsymm : ∀ (R : Type u) [CommRing R] [Algebra k R] (x y : R),
      aevalAeval x y c = aevalAeval y x c)
    (i j : ℕ) : (c.coeff j).coeff i = (c.coeff i).coeff j := by
  have h := hsymm k[X][X] (C X) X
  rw [aevalAeval_C_X_X, AlgHom.id_apply, ← swap_apply] at h
  rw [h, coeff_coeff_swap, ← h]

/-- The torsion identity, read off coefficientwise on the diagonal of degree `n`. -/
theorem coeff_tors (c : k[X][X]) (m : ℕ)
    (htors : ∀ (R : Type u) [CommRing R] [Algebra k R] (x : R),
      ∑ i ∈ range m, aevalAeval ((i : R) * x) x c = 0)
    (n : ℕ) :
    ∑ l ∈ range (n + 1), powerSum k m l * (c.coeff (n - l)).coeff l = 0 := by
  have h := congrArg (fun q : k[X] => q.coeff n) (htors k[X] X)
  simp only [finsetSum_coeff, coeff_zero] at h
  rw [← h]
  simp_rw [← C_eq_natCast, coeff_aevalAeval_C_mul_X_X, powerSum, sum_mul]
  rw [sum_comm]
  exact sum_congr rfl fun l _ => sum_congr rfl fun i _ => mul_comm _ _

/-- A normalized cocycle: the cocycle identity forces `c(0, y) = c(0, 0)`. -/
theorem coeff_zero_of_pos (c : k[X][X])
    (hrel : ∀ a b e, (if e = 0 then (c.coeff b).coeff a else 0) +
        ((a + b).choose b : k) * (c.coeff e).coeff (a + b) =
      (if a = 0 then (c.coeff e).coeff b else 0) +
        ((b + e).choose e : k) * (c.coeff (b + e)).coeff a)
    {e : ℕ} (he : 0 < e) : (c.coeff e).coeff 0 = 0 := by
  have := hrel 0 0 e
  simp only [he.ne', ↓reduceIte, zero_add, Nat.choose_self, Nat.cast_one, one_mul] at this
  linear_combination -this

/-- The homogeneous components of a symmetric 2-cocycle. -/
theorem isHomCocycle_of_coeff (c : k[X][X])
    (hsymm : ∀ i j, (c.coeff j).coeff i = (c.coeff i).coeff j)
    (hrel : ∀ a b e, (if e = 0 then (c.coeff b).coeff a else 0) +
        ((a + b).choose b : k) * (c.coeff e).coeff (a + b) =
      (if a = 0 then (c.coeff e).coeff b else 0) +
        ((b + e).choose e : k) * (c.coeff (b + e)).coeff a)
    {n : ℕ} (hn : 0 < n) : IsHomCocycle n (fun l => (c.coeff (n - l)).coeff l) := by
  have h0 : ∀ {e : ℕ}, 0 < e → (c.coeff e).coeff 0 = 0 := coeff_zero_of_pos c hrel
  refine ⟨by simpa using h0 hn, ?_, fun i hi => ?_, fun a b ha hb hab => ?_⟩
  · rw [Nat.sub_self, ← hsymm]
    exact h0 hn
  · rw [Nat.sub_sub_self hi, hsymm]
  · obtain ⟨e, rfl⟩ : ∃ e, n = a + b + e := ⟨n - a - b, by omega⟩
    have he : e ≠ 0 := by omega
    have := hrel a b e
    simp only [he, ha.ne', ↓reduceIte, zero_add] at this
    rw [show a + b + e - (a + b) = e by omega, show a + b + e - a = b + e by omega,
      Nat.choose_symm_add (a := a), Nat.choose_symm_add (a := b)]
    linear_combination this

/-- The homogeneous components of a symmetric 2-cocycle satisfying the torsion condition are
multiples of binomial coefficients. -/
theorem exists_coeff_eq_choose (c : k[X][X])
    (hsymm : ∀ i j, (c.coeff j).coeff i = (c.coeff i).coeff j)
    (hrel : ∀ a b e, (if e = 0 then (c.coeff b).coeff a else 0) +
        ((a + b).choose b : k) * (c.coeff e).coeff (a + b) =
      (if a = 0 then (c.coeff e).coeff b else 0) +
        ((b + e).choose e : k) * (c.coeff (b + e)).coeff a)
    (htors : ∀ n, ∑ l ∈ range (n + 1), powerSum k (ringChar k) l * (c.coeff (n - l)).coeff l = 0) :
    ∃ g : ℕ → k, ∀ n i, 0 < i → i < n → (c.coeff (n - i)).coeff i = g n * (n.choose i : k) := by
  have key : ∀ n, ∃ g : k, ∀ i, 0 < i → i < n →
      (c.coeff (n - i)).coeff i = g * (n.choose i : k) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨0, fun i hi hin => absurd hin (by omega)⟩
    have hc := isHomCocycle_of_coeff c hsymm hrel hn
    rcases CharP.char_is_prime_or_zero k (ringChar k) with hp | h0
    · have : Fact (ringChar k).Prime := ⟨hp⟩
      exact hc.exists_eq_charP (ringChar k) (htors n)
    · have : CharP k 0 := ringChar.of_eq h0
      have : CharZero k := CharP.charP_to_charZero k
      exact hc.exists_eq_charZero
  choose g hg using key
  exact ⟨g, hg⟩

/-- Evaluation at the inner variable is the constant embedding. -/
theorem aeval_C_X (G : k[X]) : aeval (C X : k[X][X]) G = C G := by
  rw [show (C X : k[X][X]) = (CAlgHom (R := k) (A := k[X])) X from rfl, aeval_algHom_apply,
    aeval_X_left_apply, CAlgHom_apply]

/-- **Polynomial cocycle lemma.** Over a field `k`, a symmetric polynomial 2-cocycle `c(x, y)`
satisfying the torsion condition `∑_{i < char k} c(i x, x) = 0` is a coboundary
`G(x + y) - G(x) - G(y)` of a one-variable polynomial `G`. In characteristic zero the torsion
condition is vacuous. -/
theorem exists_coboundary (c : k[X][X])
    (hsymm : ∀ (R : Type u) [CommRing R] [Algebra k R] (x y : R),
      aevalAeval x y c = aevalAeval y x c)
    (hcoc : ∀ (R : Type u) [CommRing R] [Algebra k R] (x y z : R),
      aevalAeval x y c + aevalAeval (x + y) z c = aevalAeval y z c + aevalAeval x (y + z) c)
    (htors : ∀ (R : Type u) [CommRing R] [Algebra k R] (x : R),
      ∑ i ∈ range (ringChar k), aevalAeval ((i : R) * x) x c = 0) :
    ∃ G : k[X], ∀ (R : Type u) [CommRing R] [Algebra k R] (x y : R),
      aevalAeval x y c = aeval (x + y) G - aeval x G - aeval y G := by
  have hs := coeff_symm c hsymm
  have hr := coeff_rel c hcoc
  obtain ⟨g, hg⟩ := exists_coeff_eq_choose c hs hr (coeff_tors c _ htors)
  set M := 2 * c.natDegree + 1 with hM
  obtain ⟨G, hG⟩ : ∃ G : k[X], ∀ n, G.coeff n =
      if n < M then (if n = 0 then -(c.coeff 0).coeff 0 else g n) else 0 :=
    ⟨∑ n ∈ range M, monomial n (if n = 0 then -(c.coeff 0).coeff 0 else g n), fun n => by
      simp only [finsetSum_coeff, coeff_monomial, sum_ite_eq', mem_range]⟩
  have hvanish : ∀ i j, M ≤ i + j → (c.coeff j).coeff i = 0 := by
    intro i j hij
    rcases Nat.lt_or_ge c.natDegree j with hj | hj
    · rw [coeff_eq_zero_of_natDegree_lt hj, coeff_zero]
    · rw [hs, coeff_eq_zero_of_natDegree_lt (by omega : c.natDegree < i), coeff_zero]
  have key : c = aeval (C X + X : k[X][X]) G - aeval (C X : k[X][X]) G -
      aeval (X : k[X][X]) G := by
    rw [add_comm, aeval_X_add_C_X, aeval_C_X, show aeval (X : k[X][X]) G = G.map C from rfl]
    ext j i
    simp only [coeff_sub, coeff_taylor_X_map_C, hasseDeriv_coeff, coeff_map]
    rcases Nat.eq_zero_or_pos i with rfl | hi <;> rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp [hG, hM]
    · simp [coeff_C, hj.ne', coeff_zero_of_pos c hr hj]
    · rw [hs, coeff_zero_of_pos c hr hi]
      simp [coeff_C, hi.ne']
    · simp only [coeff_C, hi.ne', hj.ne', ↓reduceIte, coeff_zero, sub_zero, hG]
      split_ifs with hn hn'
      · omega
      · have := hg (i + j) i hi (by omega)
        rw [Nat.add_sub_cancel_left] at this
        rw [this, Nat.choose_symm_add, mul_comm]
      · rw [hvanish i j (by omega), mul_zero]
  refine ⟨G, fun R _ _ x y => ?_⟩
  have h := congrArg (aevalAeval x y) key
  rwa [map_sub, map_sub, ← aeval_algHom_apply, ← aeval_algHom_apply, ← aeval_algHom_apply, map_add,
    aevalAeval_X, aevalAeval_Y] at h

end Coboundary

end Langlands.Algebra.PolynomialCocycle
