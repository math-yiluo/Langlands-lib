import Langlands.Representation.Archimedean.ComplexJacquetFinite
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Gelfand's central elements separate the shifted diagonal up to permutation

For `x : Fin n → ℂ` let `g_k(a)(x)` be the values of Gelfand's polynomials
`ComplexJacquetFinite.gelPoly n k a` at `x`, and `l_a = x_a + a`. The generating series
`G_a = ∑_k g_k(a)(x) t^k` satisfy `(1 - t ∑_a G_a) ∏_a (1 - l_a t) = ∏_a (1 - (l_a + 1) t)`.
Hence the sums `∑_a g_k(a)(x)`, `k ∈ ℕ`, determine the multiset `{l_a}`: if they agree for `x`
and `y`, then `x_a + a = y_{σ a} + σ a` for a permutation `σ` (`exists_perm_of_gel_eq`).
-/

noncomputable section

open scoped Polynomial

set_option autoImplicit false

namespace Langlands.Archimedean.GelfandSeparation

open ComplexJacquetFinite

variable {n : ℕ}

/-! ## Values of Gelfand's polynomials -/

/-- The value `g_k(a)(x)` of Gelfand's polynomial. -/
def gv (x : Fin n → ℂ) (k : ℕ) (a : Fin n) : ℂ := MvPolynomial.eval x (gelPoly n k a)

theorem gv_zero (x : Fin n → ℂ) (a : Fin n) : gv x 0 a = 1 := by
  simp [gv, gelPoly_zero]

theorem gv_succ (x : Fin n → ℂ) (k : ℕ) (a : Fin n) :
    gv x (k + 1) a = (x a + ((a : ℕ) : ℂ)) * gv x k a - ∑ c ∈ Finset.Iio a, gv x k c := by
  simp [gv, gelPoly_succ, map_sum]

/-- The shifted coordinate `l_a = x_a + a`. -/
def ll (x : Fin n → ℂ) (a : Fin n) : ℂ := x a + ((a : ℕ) : ℂ)

/-! ## Generating series -/

/-- The generating series `G_a = ∑_k g_k(a)(x) t^k`. -/
def ser (x : Fin n → ℂ) (a : Fin n) : PowerSeries ℂ := PowerSeries.mk fun k => gv x k a

theorem ser_mul (x : Fin n → ℂ) (a : Fin n) :
    ser x a * (1 - PowerSeries.C (ll x a) * PowerSeries.X) =
      1 - PowerSeries.X * ∑ c ∈ Finset.Iio a, ser x c := by
  have h : ser x a * (1 - PowerSeries.C (ll x a) * PowerSeries.X) =
      ser x a - PowerSeries.C (ll x a) * (PowerSeries.X * ser x a) := by ring
  rw [h]
  ext m
  cases m with
  | zero =>
    simp [ser, gv_zero]
  | succ k =>
    rw [map_sub, map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_succ_X_mul, map_sum]
    simp only [ser, PowerSeries.coeff_mk, PowerSeries.coeff_one, gv_succ, ll]
    simp

theorem prod_identity_aux (x : Fin n → ℂ) (m : ℕ) :
    (1 - PowerSeries.X *
        ∑ c ∈ Finset.univ.filter (fun c : Fin n => (c : ℕ) < m), ser x c) *
      ∏ c ∈ Finset.univ.filter (fun c : Fin n => (c : ℕ) < m),
        (1 - PowerSeries.C (ll x c) * PowerSeries.X) =
      ∏ c ∈ Finset.univ.filter (fun c : Fin n => (c : ℕ) < m),
        (1 - PowerSeries.C (ll x c + 1) * PowerSeries.X) := by
  induction m with
  | zero => simp
  | succ m ih =>
    by_cases hm : m < n
    · set a : Fin n := ⟨m, hm⟩ with ha
      have hfilt : Finset.univ.filter (fun c : Fin n => (c : ℕ) < m + 1) =
          insert a (Finset.univ.filter (fun c : Fin n => (c : ℕ) < m)) := by
        ext c
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, ha]
        constructor
        · intro hc
          rcases Nat.lt_succ_iff_lt_or_eq.mp hc with h | h
          · exact Or.inr h
          · exact Or.inl (Fin.ext h)
        · rintro (rfl | h)
          · exact Nat.lt_succ_self m
          · omega
      have hnot : a ∉ Finset.univ.filter (fun c : Fin n => (c : ℕ) < m) := by
        simp [ha]
      have hIio : Finset.Iio a = Finset.univ.filter (fun c : Fin n => (c : ℕ) < m) := by
        ext c
        simp [ha, Fin.lt_def]
      have hs := ser_mul x a
      rw [hIio] at hs
      rw [hfilt, Finset.sum_insert hnot, Finset.prod_insert hnot, Finset.prod_insert hnot, ← ih]
      set S := ∑ c ∈ Finset.univ.filter (fun c : Fin n => (c : ℕ) < m), ser x c
      set P := ∏ c ∈ Finset.univ.filter (fun c : Fin n => (c : ℕ) < m),
        (1 - PowerSeries.C (ll x c) * PowerSeries.X)
      calc (1 - PowerSeries.X * (ser x a + S)) *
            ((1 - PowerSeries.C (ll x a) * PowerSeries.X) * P)
          = ((1 - PowerSeries.X * S) * (1 - PowerSeries.C (ll x a) * PowerSeries.X) -
              PowerSeries.X * (ser x a * (1 - PowerSeries.C (ll x a) * PowerSeries.X))) * P := by
            ring
        _ = ((1 - PowerSeries.X * S) * (1 - PowerSeries.C (ll x a) * PowerSeries.X) -
              PowerSeries.X * (1 - PowerSeries.X * S)) * P := by rw [hs]
        _ = (1 - PowerSeries.C (ll x a + 1) * PowerSeries.X) *
              ((1 - PowerSeries.X * S) * P) := by
            rw [map_add, map_one]
            ring
    · have hfilt : Finset.univ.filter (fun c : Fin n => (c : ℕ) < m + 1) =
          Finset.univ.filter (fun c : Fin n => (c : ℕ) < m) := by
        ext c
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have := c.2
        omega
      rw [hfilt]
      exact ih

/-- `(1 - t ∑_a G_a) ∏_a (1 - l_a t) = ∏_a (1 - (l_a + 1) t)`. -/
theorem prod_identity (x : Fin n → ℂ) :
    (1 - PowerSeries.X * ∑ c, ser x c) * ∏ c, (1 - PowerSeries.C (ll x c) * PowerSeries.X) =
      ∏ c, (1 - PowerSeries.C (ll x c + 1) * PowerSeries.X) := by
  have h := prod_identity_aux x n
  have hfilt : Finset.univ.filter (fun c : Fin n => (c : ℕ) < n) = Finset.univ := by
    ext c
    simp
  rwa [hfilt] at h

/-! ## Polynomials with prescribed inverse roots -/

/-- `∏_{c ∈ A} (1 - c t)`. -/
def pol (A : Multiset ℂ) : ℂ[X] := (A.map fun c => 1 - Polynomial.C c * Polynomial.X).prod

theorem pol_add (A B : Multiset ℂ) : pol (A + B) = pol A * pol B := by
  simp [pol, Multiset.map_add, Multiset.prod_add]

theorem coe_pol (A : Multiset ℂ) :
    ((pol A : ℂ[X]) : PowerSeries ℂ) =
      (A.map fun c => 1 - PowerSeries.C c * PowerSeries.X).prod := by
  rw [← Polynomial.coeToPowerSeries.ringHom_apply, pol, map_multiset_prod, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl (fun c _ => ?_)
  simp [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C, Polynomial.coe_X]

theorem one_sub_ne_zero (c : ℂ) : (1 - Polynomial.C c * Polynomial.X : ℂ[X]) ≠ 0 := by
  intro h
  have := congrArg (fun p : ℂ[X] => p.coeff 0) h
  simp at this

theorem roots_one_sub (c : ℂ) :
    (1 - Polynomial.C c * Polynomial.X : ℂ[X]).roots = if c = 0 then 0 else {c⁻¹} := by
  split_ifs with hc
  · simp [hc]
  · have h : (1 - Polynomial.C c * Polynomial.X : ℂ[X]) =
        -(Polynomial.C c * Polynomial.X - Polynomial.C 1) := by
      rw [Polynomial.C_1]
      ring
    rw [h, Polynomial.roots_neg, Polynomial.roots_C_mul_X_sub_C _ hc, mul_one]

theorem roots_pol (A : Multiset ℂ) :
    (pol A).roots = (A.filter (fun c => c ≠ 0)).map (fun c => c⁻¹) := by
  classical
  rw [pol, Polynomial.roots_multiset_prod _ (by
    rw [Multiset.mem_map]
    rintro ⟨c, -, h⟩
    exact one_sub_ne_zero c h), Multiset.bind_map]
  induction A using Multiset.induction_on with
  | empty => simp
  | cons c A ih =>
    rw [Multiset.cons_bind, ih, roots_one_sub, Multiset.filter_cons]
    by_cases hc : c = 0
    · simp [hc]
    · simp [hc]

/-- A multiset is determined by its cardinality and `∏_{c ∈ A} (1 - c t)`. -/
theorem eq_of_pol_eq {A B : Multiset ℂ} (hcard : Multiset.card A = Multiset.card B)
    (h : pol A = pol B) : A = B := by
  classical
  have hr := congrArg Polynomial.roots h
  rw [roots_pol, roots_pol] at hr
  have hf : A.filter (fun c => c ≠ 0) = B.filter (fun c => c ≠ 0) :=
    Multiset.map_injective inv_injective hr
  have dA := Multiset.filter_add_not (fun c : ℂ => c ≠ 0) A
  have dB := Multiset.filter_add_not (fun c : ℂ => c ≠ 0) B
  have zA : A.filter (fun c : ℂ => ¬ c ≠ 0) =
      Multiset.replicate (Multiset.card (A.filter fun c : ℂ => ¬ c ≠ 0)) 0 :=
    Multiset.eq_replicate_card.2 (fun b hb => by simpa using (Multiset.mem_filter.1 hb).2)
  have zB : B.filter (fun c : ℂ => ¬ c ≠ 0) =
      Multiset.replicate (Multiset.card (B.filter fun c : ℂ => ¬ c ≠ 0)) 0 :=
    Multiset.eq_replicate_card.2 (fun b hb => by simpa using (Multiset.mem_filter.1 hb).2)
  have hc : Multiset.card (A.filter fun c : ℂ => ¬ c ≠ 0) =
      Multiset.card (B.filter fun c : ℂ => ¬ c ≠ 0) := by
    have h1 := congrArg Multiset.card dA
    have h2 := congrArg Multiset.card dB
    rw [Multiset.card_add] at h1 h2
    rw [hf] at h1
    omega
  rw [← dA, ← dB, hf, zA, zB, hc]

/-! ## Shift-invariant differences vanish -/

theorem count_map_add_one (A : Multiset ℂ) (w : ℂ) :
    Multiset.count w (A.map (· + 1)) = Multiset.count (w - 1) A := by
  have h := Multiset.count_map_eq_count' (· + 1) A (add_left_injective 1) (w - 1)
  simpa using h

/-- If `A + 1` plus `B` equals `B + 1` plus `A` (as multisets), then `A = B`. -/
theorem eq_of_shift {A B : Multiset ℂ} (h : A.map (· + 1) + B = B.map (· + 1) + A) : A = B := by
  classical
  by_contra hne
  obtain ⟨z, hz⟩ : ∃ z, Multiset.count z A ≠ Multiset.count z B := by
    by_contra h'
    push Not at h'
    exact hne (Multiset.ext.2 h')
  have hstep : ∀ w : ℂ, Multiset.count (w - 1) A = Multiset.count (w - 1) B →
      Multiset.count w A = Multiset.count w B := by
    intro w hw
    have h1 := congrArg (Multiset.count w) h
    rw [Multiset.count_add, Multiset.count_add, count_map_add_one, count_map_add_one] at h1
    omega
  have hall : ∀ m : ℕ, Multiset.count (z - m) A ≠ Multiset.count (z - m) B := by
    intro m
    induction m with
    | zero => simpa using hz
    | succ m ih =>
      intro heq
      apply ih
      apply hstep
      have : z - (m : ℂ) - 1 = z - ((m + 1 : ℕ) : ℂ) := by push_cast; ring
      rw [this]
      exact heq
  have hmem : ∀ m : ℕ, z - (m : ℂ) ∈ (A + B).toFinset := by
    intro m
    rw [Multiset.mem_toFinset, Multiset.mem_add]
    by_contra hc
    push Not at hc
    exact hall m (by rw [Multiset.count_eq_zero.2 hc.1, Multiset.count_eq_zero.2 hc.2])
  have hinj : Function.Injective (fun m : ℕ => z - (m : ℂ)) := by
    intro a b hab
    simp only [sub_right_inj, Nat.cast_inj] at hab
    exact hab
  exact Set.infinite_range_of_injective hinj
    ((A + B).toFinset.finite_toSet.subset (by rintro _ ⟨m, rfl⟩; exact hmem m))

/-! ## Permutations from equal multisets of values -/

theorem exists_perm_of_map_eq {f g : Fin n → ℂ}
    (h : (Finset.univ.val.map f : Multiset ℂ) = Finset.univ.val.map g) :
    ∃ σ : Equiv.Perm (Fin n), ∀ a, f a = g (σ a) := by
  classical
  have hc : ∀ c, Fintype.card {a // f a = c} = Fintype.card {b // g b = c} := by
    intro c
    have h1 := congrArg (Multiset.count c) h
    rw [Multiset.count_map, Multiset.count_map] at h1
    rw [Fintype.card_subtype, Fintype.card_subtype]
    have e1 : (Finset.univ.filter fun a => f a = c) = Finset.univ.filter fun a => c = f a :=
      Finset.filter_congr (fun a _ => eq_comm)
    have e2 : (Finset.univ.filter fun a => g a = c) = Finset.univ.filter fun a => c = g a :=
      Finset.filter_congr (fun a _ => eq_comm)
    rw [e1, e2]
    exact h1
  let e : ∀ c, {a // f a = c} ≃ {b // g b = c} := fun c => Fintype.equivOfCardEq (hc c)
  exact ⟨Equiv.ofFiberEquiv e, fun a => (Equiv.ofFiberEquiv_map e a).symm⟩

/-! ## Separation -/

theorem prod_eq_pol (f : Fin n → ℂ) :
    ∏ c, (1 - PowerSeries.C (f c) * PowerSeries.X) =
      ((pol (Finset.univ.val.map f) : ℂ[X]) : PowerSeries ℂ) := by
  rw [coe_pol, Multiset.map_map]
  rfl

/-- **Separation.** If `∑_a g_k(a)(x) = ∑_a g_k(a)(y)` for every `k`, then
`x_a + a = y_{σ a} + σ a` for some permutation `σ`. -/
theorem exists_perm_of_gel_eq (x y : Fin n → ℂ)
    (h : ∀ k, ∑ a, gv x k a = ∑ a, gv y k a) :
    ∃ σ : Equiv.Perm (Fin n), ∀ a, x a + ((a : ℕ) : ℂ) = y (σ a) + ((σ a : ℕ) : ℂ) := by
  have hser : ∑ c, ser x c = ∑ c, ser y c := by
    ext k
    simp only [map_sum, ser, PowerSeries.coeff_mk]
    exact h k
  have hx := prod_identity x
  have hy := prod_identity y
  rw [hser] at hx
  set F := 1 - PowerSeries.X * ∑ c, ser y c
  rw [prod_eq_pol, prod_eq_pol] at hx
  rw [prod_eq_pol, prod_eq_pol] at hy
  set Lx := (Finset.univ.val.map (ll x) : Multiset ℂ)
  set Ly := (Finset.univ.val.map (ll y) : Multiset ℂ)
  have hLx1 : (Finset.univ.val.map (fun c => ll x c + 1) : Multiset ℂ) = Lx.map (· + 1) := by
    rw [Multiset.map_map]; rfl
  have hLy1 : (Finset.univ.val.map (fun c => ll y c + 1) : Multiset ℂ) = Ly.map (· + 1) := by
    rw [Multiset.map_map]; rfl
  rw [hLx1] at hx
  rw [hLy1] at hy
  have hpol : pol (Lx.map (· + 1) + Ly) = pol (Ly.map (· + 1) + Lx) := by
    apply Polynomial.coe_injective
    rw [pol_add, pol_add, Polynomial.coe_mul, Polynomial.coe_mul, ← hx, ← hy]
    ring
  have hcard : Multiset.card (Lx.map (· + 1) + Ly) = Multiset.card (Ly.map (· + 1) + Lx) := by
    simp [Lx, Ly]
  have hL : Lx = Ly := eq_of_shift (eq_of_pol_eq hcard hpol)
  obtain ⟨σ, hσ⟩ := exists_perm_of_map_eq hL
  exact ⟨σ, fun a => hσ a⟩

end Langlands.Archimedean.GelfandSeparation
