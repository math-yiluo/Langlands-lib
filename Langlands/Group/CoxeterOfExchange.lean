import Mathlib.GroupTheory.Coxeter.Length

/-!
# Coxeter systems from a length function with the exchange property

Let `W` be a group, `s : B → W` an injective family of involutions generating `W`, and
`N : W → ℕ` a function with `N 1 = 0`, `N (w * s b) = N w ± 1`, and the right exchange
property: if `N (s b₁ ⋯ s bₙ * s b) < N (s b₁ ⋯ s bₙ)` then `s b₁ ⋯ s bₙ * s b` is the product
of the word with one letter deleted. Then `W` is a Coxeter group on the `s b`, with Coxeter
matrix `M a b = orderOf (s a * s b)` and length function `N`.

The proof follows Matsumoto's argument: two words of minimal length with the same product in
`W` have the same product in the Coxeter group of `M`. A minimal counterexample pair is
rewritten, using the exchange property, until both words alternate between two letters; then
their common length is `M a b` and the braid relation identifies them.
-/

namespace Langlands.Group

variable {B W : Type*} [Group W]

/-- The product `s b₁ * ⋯ * s bₙ` of the images of the letters of a word. -/
private def wp (s : B → W) (x : List B) : W := (x.map s).prod

@[simp] private lemma wp_nil (s : B → W) : wp s [] = 1 := by simp [wp]

@[simp] private lemma wp_cons (s : B → W) (b : B) (x : List B) :
    wp s (b :: x) = s b * wp s x := by simp [wp]

@[simp] private lemma wp_append (s : B → W) (x y : List B) :
    wp s (x ++ y) = wp s x * wp s y := by simp [wp]

@[simp] private lemma wp_singleton (s : B → W) (b : B) : wp s [b] = s b := by simp [wp]

/-- The hypotheses of `exists_coxeterSystem_of_exchange`, bundled. -/
private structure Hyp (s : B → W) (N : W → ℕ) : Prop where
  mul_self : ∀ b, s b * s b = 1
  injective : Function.Injective s
  one : N 1 = 0
  mul_simple : ∀ w b, N (w * s b) = N w + 1 ∨ N (w * s b) + 1 = N w
  exchange : ∀ (x : List B) (b : B), N (wp s x * s b) < N (wp s x) →
    ∃ k < x.length, wp s x * s b = wp s (x.eraseIdx k)
  generates : ∀ w, ∃ x : List B, wp s x = w

/-- The alternating word `a b a b ⋯` of length `n` starting with `a`. -/
private def altFrom (a b : B) : ℕ → List B
  | 0 => []
  | n + 1 => a :: altFrom b a n

private lemma altFrom_succ (a b : B) (n : ℕ) : altFrom a b (n + 1) = a :: altFrom b a n := rfl

private lemma length_altFrom (a b : B) (n : ℕ) : (altFrom a b n).length = n := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih => simp [altFrom_succ, ih]

private lemma altFrom_succ_right (a b : B) (n : ℕ) :
    altFrom a b (n + 1) = altFrom a b n ++ [if Even n then a else b] := by
  induction n generalizing a b with
  | zero => simp [altFrom]
  | succ n ih =>
    rw [altFrom_succ, ih b a, altFrom_succ]
    by_cases hn : Even n <;> simp [hn, Nat.even_add_one]

private lemma altFrom_succ_succ_right (a b : B) (n : ℕ) :
    altFrom a b (n + 1 + 1) = altFrom a b (n + 1) ++ [if Even n then b else a] := by
  rw [altFrom_succ_right a b (n + 1)]
  by_cases hn : Even n <;> simp [hn, Nat.even_add_one]

private lemma altFrom_eq_alternatingWord (a b : B) (n : ℕ) :
    altFrom a b n = CoxeterSystem.alternatingWord (if Even n then a else b)
      (if Even n then b else a) n := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih =>
    rw [altFrom_succ, ih b a, CoxeterSystem.alternatingWord_succ']
    by_cases hn : Even n <;> simp [hn, Nat.even_add_one]

private lemma wp_altFrom_two_mul_add (s : B → W) (a b : B) (k n : ℕ) :
    wp s (altFrom a b (2 * k + n)) = (s a * s b) ^ k * wp s (altFrom a b n) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) + n = 2 * k + n + 1 + 1 by ring, altFrom_succ, altFrom_succ, wp_cons,
      wp_cons, ih, pow_succ', mul_assoc, mul_assoc]

section Hyp

variable {s : B → W} {N : W → ℕ} (h : Hyp s N)
include h

private lemma inv_s (b : B) : (s b)⁻¹ = s b := inv_eq_of_mul_eq_one_right (h.mul_self b)

private lemma wp_altFrom_mul_inv (a b : B) (n : ℕ) :
    wp s (altFrom a b n) * (wp s (altFrom b a n))⁻¹ = (s a * s b) ^ n := by
  induction n generalizing a b with
  | zero => simp [altFrom]
  | succ n ih =>
    rw [altFrom_succ, altFrom_succ, wp_cons, wp_cons, mul_inv_rev, inv_s h b]
    calc s a * wp s (altFrom b a n) * ((wp s (altFrom a b n))⁻¹ * s b)
        = s a * (wp s (altFrom b a n) * (wp s (altFrom a b n))⁻¹) * s b := by
          simp only [mul_assoc]
      _ = s a * (s b * s a) ^ n * s b := by rw [ih b a]
      _ = (s a * s b) ^ (n + 1) := by
        rw [(SemiconjBy.pow_right (show SemiconjBy (s a) (s b * s a) (s a * s b) by
          simp [SemiconjBy, mul_assoc]) n).eq, pow_succ]
        simp only [mul_assoc]

private lemma mul_le (w : W) (b : B) : N (w * s b) ≤ N w + 1 := by
  rcases h.mul_simple w b with h1 | h1 <;> omega

private lemma mul_wp_le (w : W) (y : List B) : N (w * wp s y) ≤ N w + y.length := by
  induction y using List.reverseRecOn with
  | nil => simp
  | append_singleton y b ih =>
    have := mul_le h (w * wp s y) b
    simp only [wp_append, wp_singleton, List.length_append, List.length_singleton, ← mul_assoc]
    omega

private lemma wp_le (x : List B) : N (wp s x) ≤ x.length := by
  simpa [h.one] using mul_wp_le h 1 x

private lemma exists_word (w : W) : ∃ y, wp s y = w ∧ y.length = N w := by
  obtain ⟨x, rfl⟩ := h.generates w
  induction x using List.reverseRecOn with
  | nil => exact ⟨[], rfl, by simp [h.one]⟩
  | append_singleton x b ih =>
    obtain ⟨y, hy, hlen⟩ := ih
    rw [wp_append, wp_singleton]
    rw [← hy] at hlen ⊢
    rcases h.mul_simple (wp s y) b with h1 | h1
    · exact ⟨y ++ [b], by simp, by simp [h1, hlen]⟩
    · obtain ⟨k, hk, hk'⟩ := h.exchange y b (by omega)
      refine ⟨y.eraseIdx k, hk'.symm, ?_⟩
      rw [List.length_eraseIdx_of_lt hk]
      omega

private lemma le_mul (u v : W) : N (u * v) ≤ N u + N v := by
  obtain ⟨y, rfl, hy⟩ := exists_word h v
  rw [← hy]
  exact mul_wp_le h u y

end Hyp

/-- A word is reduced for `N` when its length is `N` of its product. -/
private def Red (s : B → W) (N : W → ℕ) (x : List B) : Prop := N (wp s x) = x.length

section Hyp

variable {s : B → W} {N : W → ℕ} (h : Hyp s N)
include h

private lemma red_append {x y : List B} (hr : Red s N (x ++ y)) : Red s N x ∧ Red s N y := by
  unfold Red at *
  rw [wp_append, List.length_append] at hr
  have h1 := le_mul h (wp s x) (wp s y)
  have h2 := wp_le h x
  have h3 := wp_le h y
  constructor <;> omega

/-- The Coxeter matrix of orders of products of two generators. -/
private noncomputable def cmat : CoxeterMatrix B where
  M := Matrix.of fun a b => orderOf (s a * s b)
  isSymm := by
    refine Matrix.IsSymm.ext fun a b => ?_
    simp only [Matrix.of_apply]
    rw [← orderOf_inv, mul_inv_rev, inv_s h, inv_s h]
  diagonal a := by simp [h.mul_self a]
  off_diagonal a b hab := by
    simp only [Matrix.of_apply, ne_eq, orderOf_eq_one_iff]
    intro h1
    apply hab
    apply h.injective
    calc s a = s a * s b * s b := by rw [mul_assoc, h.mul_self, mul_one]
      _ = s b := by rw [h1, one_mul]

private lemma cmat_apply (a b : B) : cmat h a b = orderOf (s a * s b) := rfl

/-- Two reduced words of length `q` with the same product in `W` have the same product in the
Coxeter group. -/
private def Good (q : ℕ) : Prop :=
  ∀ x y : List B, x.length = q → y.length = q → Red s N x → Red s N y → wp s x = wp s y →
    (cmat h).toCoxeterSystem.wordProd x = (cmat h).toCoxeterSystem.wordProd y

/-- A counterexample pair of length `q`. -/
private def Bad (q : ℕ) (u v : List B) : Prop :=
  u.length = q ∧ v.length = q ∧ Red s N u ∧ Red s N v ∧ wp s u = wp s v ∧
    (cmat h).toCoxeterSystem.wordProd u ≠ (cmat h).toCoxeterSystem.wordProd v

private lemma not_bad_append {q : ℕ} (ih : ∀ m < q, Good h m) {u v : List B} {t : B} :
    ¬ Bad h q (u ++ [t]) (v ++ [t]) := by
  rintro ⟨h1, h2, h3, h4, h5, h6⟩
  simp only [List.length_append, List.length_singleton] at h1 h2
  have hw : wp s u = wp s v := by simpa using h5
  apply h6
  rw [CoxeterSystem.wordProd_append, CoxeterSystem.wordProd_append,
    ih (q - 1) (by omega) u v (by omega) (by omega) (red_append h h3).1 (red_append h h4).1 hw]

private lemma not_bad_cons {q : ℕ} (ih : ∀ m < q, Good h m) {u v : List B} {t : B} :
    ¬ Bad h q (t :: u) (t :: v) := by
  rintro ⟨h1, h2, h3, h4, h5, h6⟩
  simp only [List.length_cons] at h1 h2
  have hw : wp s u = wp s v := by simpa using h5
  apply h6
  rw [CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_cons,
    ih (q - 1) (by omega) u v (by omega) (by omega) (red_append h (x := [t]) h3).2
      (red_append h (x := [t]) h4).2 hw]

/-- The key rewriting step: from a counterexample `(u, v ++ [t])` one gets the counterexample
`(u.tail ++ [t], u)`. -/
private lemma bad_tail {q : ℕ} (ih : ∀ m < q, Good h m) {u v : List B} {t : B}
    (hb : Bad h q u (v ++ [t])) : Bad h q (u.tail ++ [t]) u := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hb
  simp only [List.length_append, List.length_singleton] at h2
  have hv : N (wp s v) = v.length := (red_append h h4).1
  have hu : N (wp s u) = u.length := h3
  have hut : wp s u * s t = wp s v := by
    rw [h5, wp_append, wp_singleton, mul_assoc, h.mul_self, mul_one]
  have hlt : N (wp s u * s t) < N (wp s u) := by
    rw [hut]
    omega
  obtain ⟨k, hk, hk'⟩ := h.exchange u t hlt
  have hlen : (u.eraseIdx k).length = q - 1 := by
    rw [List.length_eraseIdx_of_lt hk]
    omega
  have he : wp s (u.eraseIdx k) = wp s v := by rw [← hk', hut]
  have hred : Red s N (u.eraseIdx k) := by
    unfold Red
    rw [he, hv, hlen]
    omega
  have hG : (cmat h).toCoxeterSystem.wordProd (u.eraseIdx k) =
      (cmat h).toCoxeterSystem.wordProd v :=
    ih (q - 1) (by omega) _ _ hlen (by omega) hred (red_append h h4).1 he
  have hz1 : wp s (u.eraseIdx k ++ [t]) = wp s u := by
    rw [wp_append, wp_singleton, ← hk', mul_assoc, h.mul_self, mul_one]
  have hz2 : (u.eraseIdx k ++ [t]).length = q := by
    simp only [List.length_append, List.length_singleton, hlen]
    omega
  have hz3 : Red s N (u.eraseIdx k ++ [t]) := by
    unfold Red
    rw [hz1, hz2, hu, h1]
  have hz4 : (cmat h).toCoxeterSystem.wordProd (u.eraseIdx k ++ [t]) ≠
      (cmat h).toCoxeterSystem.wordProd u := by
    rw [CoxeterSystem.wordProd_append, hG, ← CoxeterSystem.wordProd_append]
    exact Ne.symm h6
  cases k with
  | zero =>
    rw [List.eraseIdx_zero] at hz1 hz2 hz3 hz4
    exact ⟨hz2, h1, hz3, h3, hz1, hz4⟩
  | succ k =>
    exfalso
    obtain _ | ⟨c, u1⟩ := u
    · simp at hk
    · rw [List.eraseIdx_cons_succ, List.cons_append] at hz1 hz2 hz3 hz4
      exact not_bad_cons h ih ⟨hz2, h1, hz3, h3, hz1, hz4⟩

/-- Iterating `bad_tail` from a counterexample `(x0 ++ [b], y0 ++ [a])`. -/
private lemma bad_iter {q : ℕ} (ih : ∀ m < q, Good h m) {x0 y0 : List B} {a b : B}
    (hb : Bad h q (x0 ++ [b]) (y0 ++ [a])) :
    ∀ n, n + 1 ≤ q →
      ∃ V, Bad h q (x0.drop n ++ altFrom b a (n + 1)) (V ++ [if Even n then a else b]) := by
  have hx0 : x0.length + 1 = q := by simpa using hb.1
  intro n
  induction n with
  | zero =>
    intro _
    refine ⟨y0, ?_⟩
    simpa [altFrom] using hb
  | succ n ihn =>
    intro hn
    obtain ⟨V, hV⟩ := ihn (by omega)
    have h' := bad_tail h ih hV
    have hne : x0.drop n ≠ [] := by
      intro h0
      have := congrArg List.length h0
      simp at this
      omega
    have e1 : (x0.drop n ++ altFrom b a (n + 1)).tail ++ [if Even n then a else b] =
        x0.drop (n + 1) ++ altFrom b a (n + 1 + 1) := by
      rw [List.tail_append_of_ne_nil hne, List.tail_drop, List.append_assoc,
        altFrom_succ_succ_right b a n]
    have e2 : x0.drop n ++ altFrom b a (n + 1) =
        (x0.drop n ++ altFrom b a n) ++ [if Even (n + 1) then a else b] := by
      rw [altFrom_succ_right, List.append_assoc]
      by_cases hn : Even n <;> simp [hn, Nat.even_add_one]
    rw [e1, e2] at h'
    exact ⟨_, h'⟩

/-- Two alternating words never form a counterexample. -/
private lemma not_bad_alt {q : ℕ} (a b : B) : ¬ Bad h q (altFrom a b q) (altFrom b a q) := by
  rintro ⟨-, -, h3, -, h5, h6⟩
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · exact h6 rfl
  have hpow : (s a * s b) ^ q = 1 := by
    rw [← wp_altFrom_mul_inv h, h5, mul_inv_cancel]
  have hdvd : orderOf (s a * s b) ∣ q := orderOf_dvd_of_pow_eq_one hpow
  have hqm : q = orderOf (s a * s b) := by
    by_contra hne
    obtain ⟨c, hc⟩ := hdvd
    have hc0 : c ≠ 0 := by
      rintro rfl
      simp at hc
      omega
    have hc1 : c ≠ 1 := by
      rintro rfl
      simp at hc
      exact hne hc
    have h2m : 2 * orderOf (s a * s b) ≤ q :=
      calc 2 * orderOf (s a * s b) = orderOf (s a * s b) * 2 := mul_comm _ _
        _ ≤ orderOf (s a * s b) * c := Nat.mul_le_mul_left _ (by omega)
        _ = q := hc.symm
    have hsplit : q = 2 * orderOf (s a * s b) + (q - 2 * orderOf (s a * s b)) := by omega
    have hred : N (wp s (altFrom a b q)) = q := by
      rw [show N (wp s (altFrom a b q)) = (altFrom a b q).length from h3, length_altFrom]
    have hwp : wp s (altFrom a b q) = wp s (altFrom a b (q - 2 * orderOf (s a * s b))) := by
      conv_lhs => rw [hsplit]
      rw [wp_altFrom_two_mul_add, pow_orderOf_eq_one, one_mul]
    have hle := wp_le h (altFrom a b (q - 2 * orderOf (s a * s b)))
    rw [← hwp, hred, length_altFrom] at hle
    have hm : 0 < orderOf (s a * s b) := Nat.pos_of_dvd_of_pos ⟨c, hc⟩ hq
    omega
  apply h6
  have hab : cmat h a b = q := hqm.symm
  have hba : cmat h b a = q := by rw [(cmat h).symmetric]; exact hab
  have hbraid := (cmat h).toCoxeterSystem.wordProd_braidWord_eq a b
  simp only [CoxeterSystem.braidWord, hab, hba] at hbraid
  rw [altFrom_eq_alternatingWord, altFrom_eq_alternatingWord]
  by_cases hq2 : Even q
  · simpa [hq2] using hbraid
  · simpa [hq2] using hbraid.symm

/-- Matsumoto's lemma: reduced words with the same product in `W` have the same product in the
Coxeter group. -/
private lemma good (q : ℕ) : Good h q := by
  induction q using Nat.strong_induction_on with
  | _ q ih =>
  intro x y hx hy hrx hry hxy
  by_contra hne
  have hb : Bad h q x y := ⟨hx, hy, hrx, hry, hxy, hne⟩
  rcases List.eq_nil_or_concat' x with rfl | ⟨x0, b, rfl⟩
  · simp only [List.length_nil] at hx
    subst hx
    rw [List.length_eq_zero_iff] at hy
    subst hy
    exact hne rfl
  rcases List.eq_nil_or_concat' y with rfl | ⟨y0, a, rfl⟩
  · simp only [List.length_nil, List.length_append, List.length_singleton] at hx hy
    omega
  simp only [List.length_append, List.length_singleton] at hx
  obtain ⟨V, hV⟩ := bad_iter h ih hb (q - 1) (by omega)
  rw [List.drop_eq_nil_of_le (by omega), List.nil_append, show q - 1 + 1 = q by omega] at hV
  have h' := bad_tail h ih hV
  have e : (altFrom b a q).tail ++ [if Even (q - 1) then a else b] = altFrom a b q := by
    obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
    rw [altFrom_succ, List.tail_cons, Nat.add_sub_cancel, altFrom_succ_right]
  rw [e] at h'
  exact not_bad_alt h a b h'

/-- Every element of the Coxeter group is the product of a reduced word. -/
private lemma exists_red (g : (cmat h).Group) :
    ∃ z, Red s N z ∧ (cmat h).toCoxeterSystem.wordProd z = g := by
  obtain ⟨x, rfl⟩ := (cmat h).toCoxeterSystem.wordProd_surjective g
  induction x using List.reverseRecOn with
  | nil => exact ⟨[], by simp [Red, h.one], rfl⟩
  | append_singleton x b ih =>
    obtain ⟨z, hz, hzx⟩ := ih
    rw [CoxeterSystem.wordProd_append, ← hzx]
    have hz' : N (wp s z) = z.length := hz
    rcases h.mul_simple (wp s z) b with h1 | h1
    · refine ⟨z ++ [b], ?_, by rw [CoxeterSystem.wordProd_append]⟩
      unfold Red
      simp [h1, hz']
    · obtain ⟨k, hk, hk'⟩ := h.exchange z b (by omega)
      have hlen := List.length_eraseIdx_of_lt hk
      have hzk : Red s N (z.eraseIdx k) := by
        unfold Red
        rw [← hk', hlen]
        omega
      refine ⟨z.eraseIdx k, hzk, ?_⟩
      have hwz : wp s (z.eraseIdx k ++ [b]) = wp s z := by
        rw [wp_append, wp_singleton, ← hk', mul_assoc, h.mul_self, mul_one]
      have hG := good h z.length (z.eraseIdx k ++ [b]) z
        (by simp only [List.length_append, List.length_singleton, hlen]; omega) rfl
        (by
          unfold Red
          rw [hwz, hz']
          simp only [List.length_append, List.length_singleton, hlen]
          omega)
        hz hwz
      rw [CoxeterSystem.wordProd_append] at hG
      rw [← hG, mul_assoc, CoxeterSystem.wordProd_singleton,
        CoxeterSystem.simple_mul_simple_self, mul_one]

end Hyp

/-- **Coxeter systems from the exchange property.** Let `s : B → W` be an injective family of
involutions generating the group `W`, and let `N : W → ℕ` satisfy `N 1 = 0`,
`N (w * s b) = N w ± 1`, and the right exchange property. Then there is a Coxeter system on `W`
with Coxeter matrix `M a b = orderOf (s a * s b)`, simple reflections `s` and length `N`. -/
theorem exists_coxeterSystem_of_exchange (s : B → W) (N : W → ℕ)
    (mul_self : ∀ b, s b * s b = 1) (injective : Function.Injective s) (one : N 1 = 0)
    (mul_simple : ∀ w b, N (w * s b) = N w + 1 ∨ N (w * s b) + 1 = N w)
    (exchange : ∀ (x : List B) (b : B), N ((x.map s).prod * s b) < N (x.map s).prod →
      ∃ k < x.length, (x.map s).prod * s b = ((x.eraseIdx k).map s).prod)
    (generates : ∀ w, ∃ x : List B, (x.map s).prod = w) :
    ∃ (Mx : CoxeterMatrix B) (cs : CoxeterSystem Mx W),
      (∀ a b, Mx a b = orderOf (s a * s b)) ∧ (∀ b, cs.simple b = s b) ∧
        ∀ w, cs.length w = N w := by
  have h : Hyp s N := ⟨mul_self, injective, one, mul_simple, exchange, generates⟩
  have hl : (cmat h).IsLiftable s := fun a b => pow_orderOf_eq_one (s a * s b)
  obtain ⟨φ, hφs⟩ : ∃ φ : (cmat h).Group →* W, ∀ b, φ ((cmat h).toCoxeterSystem.simple b) = s b :=
    ⟨_, (cmat h).toCoxeterSystem.lift_apply_simple hl⟩
  have hφ : ∀ x, φ ((cmat h).toCoxeterSystem.wordProd x) = wp s x := by
    intro x
    induction x with
    | nil => simp
    | cons b x ih => rw [CoxeterSystem.wordProd_cons, map_mul, ih, hφs, wp_cons]
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    obtain ⟨z, hz, rfl⟩ := exists_red h g
    rw [hφ] at hg
    have hz0 : z.length = 0 := by
      have hz' : N (wp s z) = z.length := hz
      rw [hg, h.one] at hz'
      omega
    rw [List.length_eq_zero_iff.mp hz0, CoxeterSystem.wordProd_nil]
  have hsurj : Function.Surjective φ := by
    intro w
    obtain ⟨x, rfl⟩ := generates w
    exact ⟨_, hφ x⟩
  let e := MulEquiv.ofBijective φ ⟨hinj, hsurj⟩
  let cs : CoxeterSystem (cmat h) W := ⟨e.symm⟩
  have hs : ∀ b, cs.simple b = s b := fun b => hφs b
  refine ⟨cmat h, cs, fun a b => rfl, hs, fun w => le_antisymm ?_ ?_⟩
  · have hwp : ∀ x, cs.wordProd x = wp s x := by
      intro x
      simp [CoxeterSystem.wordProd, wp, show cs.simple = s from funext hs]
    obtain ⟨y, hy, hlen⟩ := exists_word h w
    rw [← hlen, ← hy, ← hwp]
    exact cs.length_wordProd_le y
  · obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
    have hwp : cs.wordProd ω = wp s ω := by
      simp [CoxeterSystem.wordProd, wp, show cs.simple = s from funext hs]
    rw [hω.eq, hwp]
    exact wp_le h ω

end Langlands.Group
