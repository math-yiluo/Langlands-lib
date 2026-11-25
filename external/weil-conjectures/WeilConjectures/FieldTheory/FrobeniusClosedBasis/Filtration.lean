/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal

/-!
# Frobenius-closed bases from a Frobenius-compatible filtration

Let `k` be a perfect field of characteristic `p` and `E` a `k`-algebra which is a field. Suppose
`F : ℕ → Submodule k E` is an exhaustive increasing filtration with `F 0 = k`, such that
`f ∈ F n → f ^ p ∈ F (p * n)` and `f ^ p ∈ F n → f ∈ F (n / p)`. Then `E` has a
*Frobenius-closed* `k`-basis: a family `w : ι → E` such that `1` together with the
`w i ^ p ^ r` form a `k`-basis of `E`.

This is the linear-algebra part of Kuhlmann, *Additive polynomials and their role in the
model theory of valued fields*, Theorem 10 / Lemma 26.
-/

@[expose] public section

universe v

open Submodule

namespace FrobeniusClosedBasis

section LinearAlgebra

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- Linear independence modulo a submodule, in terms of finite sums. -/
theorem linearIndependent_mkQ_iff' (U : Submodule R M) {α : Type*} (v : α → M) :
    LinearIndependent R (U.mkQ ∘ v) ↔
      ∀ (s : Finset α) (g : α → R), ∑ i ∈ s, g i • v i ∈ U → ∀ i ∈ s, g i = 0 := by
  rw [linearIndependent_iff']
  refine forall₂_congr fun s g ↦ ?_
  rw [← Submodule.Quotient.mk_eq_zero, ← mkQ_apply, map_sum]
  simp

/-- If `a` is linearly independent modulo `U ⊔ V` and `b` is a family in `V` which is linearly
independent modulo `U`, then `Sum.elim a b` is linearly independent modulo `U`. -/
theorem linearIndependent_mkQ_sumElim (U V : Submodule R M) {α β : Type*} {a : α → M}
    {b : β → M} (ha : LinearIndependent R ((U ⊔ V).mkQ ∘ a))
    (hb : LinearIndependent R (U.mkQ ∘ b)) (hbV : ∀ j, b j ∈ V) :
    LinearIndependent R (U.mkQ ∘ Sum.elim a b) := by
  have hfa : (U ⊔ V).mkQ ∘ a = U.factor le_sup_left ∘ (U.mkQ ∘ a) := by
    ext
    simp
  rw [hfa] at ha
  rw [Sum.comp_elim, linearIndependent_sum, Sum.elim_comp_inl, Sum.elim_comp_inr]
  refine ⟨ha.of_comp, hb, (Submodule.range_ker_disjoint ha).mono_right ?_⟩
  rw [span_le]
  rintro _ ⟨j, rfl⟩
  simpa using mem_sup_right (hbV j)

/-- A family `u` graded by a level function `lev`, such that `u t` lies in `H (lev t + 1)` and the
elements of each level `N` are linearly independent modulo `H N`, is linearly independent modulo
`H 0`. -/
theorem linearIndependent_mkQ_of_level {Ω : Type*} (u : Ω → M) (lev : Ω → ℕ)
    (H : ℕ → Submodule R M) (hH : Monotone H) (hu : ∀ t, u t ∈ H (lev t + 1))
    (hli : ∀ N, LinearIndependent R (fun t : {t // lev t = N} ↦ (H N).mkQ (u t))) :
    LinearIndependent R ((H 0).mkQ ∘ u) := by
  classical
  have top (n : ℕ) (s : Finset Ω) (g : Ω → R) (hs : ∀ t ∈ s, lev t ≤ n)
      (hsum : ∑ t ∈ s, g t • u t ∈ H n) (t : Ω) (ht : t ∈ s) (htn : lev t = n) : g t = 0 := by
    have hlow : ∑ t ∈ s.filter (lev · ≠ n), g t • u t ∈ H n :=
      sum_mem fun t ht ↦ smul_mem _ _ <| hH (by
        rw [Finset.mem_filter] at ht
        have := hs t ht.1
        omega) (hu t)
    have hhigh : ∑ t ∈ s.filter (lev · = n), g t • u t ∈ H n := by
      rw [← Finset.sum_filter_add_sum_filter_not s (lev · = n)] at hsum
      simpa using (H n).sub_mem hsum hlow
    have hli' := (linearIndependent_mkQ_iff' (H n) (fun t : {t // lev t = n} ↦ u t)).1 (hli n)
    refine hli' (s.subtype (lev · = n)) (fun t ↦ g t) ?_ ⟨t, htn⟩ (by simp [ht])
    rwa [Finset.sum_subtype_eq_sum_filter (f := fun t ↦ g t • u t)]
  have key (n : ℕ) (s : Finset Ω) (g : Ω → R) (hs : ∀ t ∈ s, lev t ≤ n)
      (hsum : ∑ t ∈ s, g t • u t ∈ H 0) (t : Ω) (ht : t ∈ s) : g t = 0 := by
    induction n generalizing s with
    | zero => exact top 0 s g hs hsum t ht (by have := hs t ht; omega)
    | succ n ih =>
      have htop := top (n + 1) s g hs (hH (Nat.zero_le _) hsum)
      by_cases htn : lev t = n + 1
      · exact htop t ht htn
      · rw [← Finset.sum_filter_of_ne (p := (lev · ≠ n + 1)) fun t ht h ↦ ?_] at hsum
        · refine ih (s.filter (lev · ≠ n + 1)) (fun t ht ↦ ?_) hsum (by simp [ht, htn])
          rw [Finset.mem_filter] at ht
          have := hs t ht.1
          omega
        · intro hlev
          exact h (by rw [htop t ht hlev, zero_smul])
  rw [linearIndependent_mkQ_iff']
  intro s g hsum t ht
  exact key (s.sup lev) s g (fun t ht ↦ Finset.le_sup ht) hsum t ht

end LinearAlgebra

section Frobenius

variable {k E : Type*} [Field k] [Field E] [Algebra k E] {p : ℕ} [Fact p.Prime] [CharP E p]

/-- If the `p`-th powers of the elements of `s` lie in the `k`-span of `t`, then so do the
`p`-th powers of all elements of the `k`-span of `s`. -/
theorem pow_mem_span_of_pow_mem {s t : Set E} (hs : ∀ x ∈ s, x ^ p ∈ span k t) {f : E}
    (hf : f ∈ span k s) : f ^ p ∈ span k t := by
  induction hf using Submodule.span_induction with
  | mem x hx => exact hs x hx
  | zero => simp [zero_pow (Fact.out : p.Prime).ne_zero]
  | add x y _ _ hx hy =>
    rw [add_pow_char]
    exact add_mem hx hy
  | smul c x _ hx =>
    rw [smul_pow]
    exact smul_mem _ _ hx

/-- Over a perfect field, the Frobenius map transports linear independence modulo `U` to linear
independence modulo `U'`, provided `f ^ p ∈ U'` implies `f ∈ U`. -/
theorem linearIndependent_mkQ_pow (hk : ∀ c : k, ∃ d, d ^ p = c) {U U' : Submodule k E}
    (hUU' : ∀ f, f ^ p ∈ U' → f ∈ U) {α : Type*} {v : α → E}
    (hv : LinearIndependent k (U.mkQ ∘ v)) :
    LinearIndependent k (U'.mkQ ∘ fun a ↦ v a ^ p) := by
  choose d hd using hk
  rw [linearIndependent_mkQ_iff'] at hv ⊢
  intro s g hg i hi
  have hsum : (∑ a ∈ s, d (g a) • v a) ^ p = ∑ a ∈ s, g a • v a ^ p := by
    rw [sum_pow_char]
    simp [smul_pow, hd]
  rw [← hd (g i), hv s (fun a ↦ d (g a)) (hUU' _ (hsum ▸ hg)) i hi,
    zero_pow (Fact.out : p.Prime).ne_zero]

end Frobenius

section Construction

variable {k : Type*} {E : Type v} [Field k] [Field E] [Algebra k E]

/-- Given submodules `D` and `F`, there is a family in `F`, linearly independent modulo `D`,
which together with `D` spans `F`. -/
theorem exists_linearIndependent_mkQ_sup_span (D F : Submodule k E) :
    ∃ (J : Type v) (b : J → E), (∀ j, b j ∈ F) ∧ LinearIndependent k (D.mkQ ∘ b) ∧
      F ≤ D ⊔ span k (Set.range b) := by
  obtain ⟨t, ht, hspan, hli⟩ := exists_linearIndependent k (D.mkQ '' F)
  choose b hbF hb using fun x : t ↦ ht x.2
  have hb' : D.mkQ ∘ b = Subtype.val := funext hb
  refine ⟨t, b, hbF, hb' ▸ hli, fun f hf ↦ ?_⟩
  rw [← Submodule.comap_map_mkQ, mem_comap, map_span, ← Set.range_comp, hb',
    Subtype.range_coe, hspan]
  exact subset_span ⟨f, hf, rfl⟩

/-- A leveled version of `exists_linearIndependent_mkQ_sup_span`: for every level `N ≥ 1`, a
family of elements of `F N`, linearly independent modulo `D N`, spanning `F N` modulo `D N`. -/
theorem exists_leveled_family (D F : ℕ → Submodule k E) :
    ∃ (ι : Type v) (lv : ι → ℕ) (w : ι → E), (∀ i, 1 ≤ lv i) ∧ (∀ i, w i ∈ F (lv i)) ∧
      (∀ N, LinearIndependent k (fun i : {i // lv i = N} ↦ (D N).mkQ (w i))) ∧
      ∀ N, 1 ≤ N → F N ≤ D N ⊔ span k (Set.range (fun i : {i // lv i = N} ↦ w i)) := by
  choose J b hbF hli hspan using fun N ↦ exists_linearIndependent_mkQ_sup_span (D N) (F N)
  refine ⟨Σ n, J (n + 1), fun i ↦ i.1 + 1, fun i ↦ b (i.1 + 1) i.2, fun i ↦ Nat.le_add_left 1 _,
    fun i ↦ hbF _ _, ?_, ?_⟩
  · rintro (_ | n)
    · have : IsEmpty {i : Σ n, J (n + 1) // i.1 + 1 = 0} := ⟨fun i ↦ by omega⟩
      exact linearIndependent_empty_type
    · let e : {i : Σ n, J (n + 1) // i.1 + 1 = n + 1} ≃ J (n + 1) :=
        (Equiv.subtypeEquivRight fun i ↦ by omega).trans (Equiv.sigmaSubtype n)
      have he : (fun i : {i : Σ n, J (n + 1) // i.1 + 1 = n + 1} ↦
          (D (n + 1)).mkQ (b (i.1.1 + 1) i.1.2)) = ((D (n + 1)).mkQ ∘ b (n + 1)) ∘ e := by
        funext ⟨⟨m, j⟩, h⟩
        obtain rfl : m = n := by simpa using h
        rfl
      rw [he, linearIndependent_equiv]
      exact hli _
  · rintro (_ | n) hN
    · omega
    · refine (hspan (n + 1)).trans (sup_le_sup_left (span_mono ?_) _)
      rintro _ ⟨j, rfl⟩
      exact ⟨⟨⟨n, j⟩, rfl⟩, rfl⟩

end Construction

section Main

variable {k : Type*} {E : Type v} [Field k] [Field E] [Algebra k E]

theorem _root_.Nat.sub_one_div_of_dvd {p N : ℕ} (hp : 0 < p) (hpN : p ∣ N) :
    (N - 1) / p = N / p - 1 := by
  obtain ⟨q, rfl⟩ := hpN
  rcases q with _ | q
  · simp
  · have h : p * (q + 1) - 1 = (p - 1) + p * q := by
      rw [mul_add, mul_one]
      omega
    rw [h, Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt (by omega),
      Nat.mul_div_cancel_left _ hp]
    simp

/-- **Frobenius-closed bases from a filtration** (Kuhlmann, Theorem 10 / Lemma 26).
Let `k` be a perfect field of characteristic `p` and `F` an exhaustive increasing filtration of
the field `E ⊇ k` by `k`-subspaces with `F 0 = k`, compatible with the Frobenius in the sense
that `f ∈ F n → f ^ p ∈ F (p * n)` and `f ^ p ∈ F n → f ∈ F (n / p)`. Then there is a family
`w : ι → E` such that `1` together with the `w i ^ p ^ r` form a `k`-basis of `E`. -/
theorem exists_frobeniusClosed_basis_of_filtration (p : ℕ) [Fact p.Prime] [CharP E p]
    (hk : ∀ c : k, ∃ d, d ^ p = c) (F : ℕ → Submodule k E) (hmono : Monotone F)
    (hexh : ∀ f, ∃ n, f ∈ F n) (h1 : (1 : E) ∈ F 0)
    (h0 : ∀ f ∈ F 0, ∃ c, algebraMap k E c = f)
    (hpow : ∀ n f, f ∈ F n → f ^ p ∈ F (p * n))
    (hroot : ∀ n f, f ^ p ∈ F n → f ∈ F (n / p)) :
    ∃ (ι : Type v) (w : ι → E),
      LinearIndependent k (fun j : Option (ι × ℕ) ↦ j.elim 1 (fun i ↦ w i.1 ^ p ^ i.2)) ∧
      span k (Set.range (fun j : Option (ι × ℕ) ↦ j.elim 1 (fun i ↦ w i.1 ^ p ^ i.2))) = ⊤ := by
  have hp := (Fact.out : p.Prime)
  obtain ⟨ι, lv, w, hlv, hwF, hli, hspan⟩ :=
    exists_leveled_family (fun N ↦ F (N - 1) ⊔ span k ((· ^ p) '' F (N / p))) F
  refine ⟨ι, w, ?_, ?_⟩
  · have hS (i : ι) (r : ℕ) : w i ^ p ^ r ∈ F (p ^ r * lv i) := by
      induction r with
      | zero => simpa using hwF i
      | succ r ih =>
        rw [pow_succ, pow_mul, mul_comm (p ^ r), mul_assoc]
        exact hpow _ _ ih
    have hlevel (N : ℕ) : LinearIndependent k
        (fun t : {t : ι × ℕ // p ^ t.2 * lv t.1 = N} ↦ (F (N - 1)).mkQ (w t.1.1 ^ p ^ t.1.2)) := by
      induction N using Nat.strong_induction_on with
      | _ N ih =>
      rcases Nat.eq_zero_or_pos N with rfl | hN
      · have : IsEmpty {t : ι × ℕ // p ^ t.2 * lv t.1 = 0} :=
          ⟨fun t ↦ (Nat.mul_pos (pow_pos hp.pos _) (hlv _)).ne' t.2⟩
        exact linearIndependent_empty_type
      let P : {t : ι × ℕ // p ^ t.2 * lv t.1 = N} → Prop := fun t ↦ t.1.2 = 0
      rw [← linearIndependent_equiv (Equiv.sumCompl P)]
      have heq : (fun t : {t : ι × ℕ // p ^ t.2 * lv t.1 = N} ↦
            (F (N - 1)).mkQ (w t.1.1 ^ p ^ t.1.2)) ∘ Equiv.sumCompl P =
          (F (N - 1)).mkQ ∘ Sum.elim (fun t : {t // P t} ↦ w t.1.1.1 ^ p ^ t.1.1.2)
            (fun t : {t // ¬ P t} ↦ w t.1.1.1 ^ p ^ t.1.1.2) := by
        ext (t | t) <;> rfl
      rw [heq]
      refine linearIndependent_mkQ_sumElim _ (span k ((· ^ p) '' F (N / p))) ?_ ?_ ?_
      · let φ : {t // P t} → {i // lv i = N} := fun t ↦ ⟨t.1.1.1, by
          obtain ⟨⟨⟨i, r⟩, h⟩, hr⟩ := t
          simp only [P] at hr
          subst hr
          simpa using h⟩
        have hφ : Function.Injective φ := by
          rintro ⟨⟨⟨i, r⟩, h⟩, hr⟩ ⟨⟨⟨i', r'⟩, h'⟩, hr'⟩ hii'
          simp only [P] at hr hr'
          subst hr hr'
          simp only [φ, Subtype.mk.injEq] at hii'
          subst hii'
          rfl
        have hfun : (F (N - 1) ⊔ span k ((· ^ p) '' F (N / p))).mkQ ∘
            (fun t : {t // P t} ↦ w t.1.1.1 ^ p ^ t.1.1.2) =
            (fun i : {i // lv i = N} ↦
              (F (N - 1) ⊔ span k ((· ^ p) '' F (N / p))).mkQ (w i)) ∘ φ := by
          funext ⟨⟨⟨i, r⟩, h⟩, hr⟩
          simp only [P] at hr
          subst hr
          simp [φ]
        rw [hfun]
        exact (hli N).comp φ hφ
      · rcases isEmpty_or_nonempty {t // ¬ P t} with hem | ⟨⟨⟨⟨i₀, r₀⟩, h₀⟩, hr₀⟩⟩
        · exact linearIndependent_empty_type
        have hpN : p ∣ N := by
          rw [← h₀]
          exact Dvd.dvd.mul_right (dvd_pow_self p hr₀) _
        have hlev (t : {t // ¬ P t}) : p ^ (t.1.1.2 - 1) * lv t.1.1.1 = N / p := by
          obtain ⟨⟨⟨i, r⟩, h⟩, hr⟩ := t
          obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr
          have h' : p * (p ^ r * lv i) = N := by
            rw [← h, pow_succ']
            ring
          dsimp only
          rw [← h', Nat.mul_div_cancel_left _ hp.pos]
          simp
        let ψ : {t // ¬ P t} → {t : ι × ℕ // p ^ t.2 * lv t.1 = N / p} :=
          fun t ↦ ⟨(t.1.1.1, t.1.1.2 - 1), hlev t⟩
        have hψ : Function.Injective ψ := by
          rintro ⟨⟨⟨i, r⟩, h⟩, hr⟩ ⟨⟨⟨i', r'⟩, h'⟩, hr'⟩ hii'
          simp only [ψ, Subtype.mk.injEq, Prod.mk.injEq] at hii'
          simp only [P] at hr hr'
          obtain ⟨rfl, hrr⟩ := hii'
          obtain rfl : r = r' := by omega
          rfl
        have := linearIndependent_mkQ_pow hk (U' := F (N - 1)) (fun f hf ↦ ?_)
          ((ih (N / p) (Nat.div_lt_self hN hp.one_lt)).comp ψ hψ)
        · have hfun : (fun t : {t // ¬ P t} ↦ w t.1.1.1 ^ p ^ t.1.1.2) =
              fun a ↦ (w (ψ a).1.1 ^ p ^ (ψ a).1.2) ^ p := by
            funext ⟨⟨⟨i, r⟩, h⟩, hr⟩
            obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr
            simp [ψ, pow_succ, pow_mul]
          rw [hfun]
          exact this
        · rw [← Nat.sub_one_div_of_dvd hp.pos hpN]
          exact hroot _ _ hf
      · rintro ⟨⟨⟨i, r⟩, h⟩, hr⟩
        obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr
        refine subset_span ⟨w i ^ p ^ r, ?_, ?_⟩
        · have h' : p * (p ^ r * lv i) = N := by
            rw [← h, pow_succ']
            ring
          rw [← h', Nat.mul_div_cancel_left _ hp.pos]
          exact hS i r
        · simp [pow_succ, pow_mul]
    have hglue := linearIndependent_mkQ_of_level (fun t : ι × ℕ ↦ w t.1 ^ p ^ t.2)
      (fun t ↦ p ^ t.2 * lv t.1) (fun N ↦ F (N - 1)) (fun a b hab ↦ hmono (by omega))
      (fun t ↦ by simpa using hS t.1 t.2) hlevel
    have hfam : (fun j : Option (ι × ℕ) ↦ j.elim 1 (fun i ↦ w i.1 ^ p ^ i.2)) =
        fun o ↦ o.casesOn' 1 (fun i ↦ w i.1 ^ p ^ i.2) := by
      funext o
      cases o <;> rfl
    rw [hfam, linearIndependent_option']
    refine ⟨hglue.of_comp, fun h ↦ ?_⟩
    have hdisj := Submodule.range_ker_disjoint hglue
    rw [ker_mkQ] at hdisj
    exact one_ne_zero (hdisj.le_bot ⟨h, h1⟩)
  · set T := span k (Set.range (fun j : Option (ι × ℕ) ↦ j.elim 1 (fun i ↦ w i.1 ^ p ^ i.2)))
    have hTw (i : ι) (r : ℕ) : w i ^ p ^ r ∈ T := subset_span ⟨some (i, r), rfl⟩
    have hTpow (f : E) (hf : f ∈ T) : f ^ p ∈ T := by
      refine pow_mem_span_of_pow_mem (fun x hx ↦ ?_) hf
      obtain ⟨_ | ⟨i, r⟩, rfl⟩ := hx
      · exact subset_span ⟨none, by simp⟩
      · simpa [← pow_mul, ← pow_succ] using hTw i (r + 1)
    have hF (N : ℕ) : F N ≤ T := by
      induction N using Nat.strong_induction_on with
      | _ N ih =>
      rcases Nat.eq_zero_or_pos N with rfl | hN
      · intro f hf
        obtain ⟨c, rfl⟩ := h0 f hf
        rw [Algebra.algebraMap_eq_smul_one]
        exact smul_mem _ _ (subset_span ⟨none, rfl⟩)
      refine (hspan N hN).trans (sup_le (sup_le (ih _ (by omega)) ?_) ?_)
      · rw [span_le]
        rintro _ ⟨f, hf, rfl⟩
        exact hTpow f (ih _ (Nat.div_lt_self hN hp.one_lt) hf)
      · rw [span_le]
        rintro _ ⟨i, rfl⟩
        simpa using hTw i.1 0
    rw [eq_top_iff]
    intro f _
    obtain ⟨n, hn⟩ := hexh f
    exact hF n hn

end Main

end FrobeniusClosedBasis
