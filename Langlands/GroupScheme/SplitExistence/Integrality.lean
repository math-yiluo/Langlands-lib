import Langlands.GroupScheme.SplitExistence.OdePeel
import Mathlib.Tactic.NoncommRing
import Mathlib.RingTheory.Int.Basic

/-! # Integrality of the parameters of ordered products of root exponentials

Let `S` be a commutative ring, `Z ⊆ S` a subring and `h : X →+ ℤ`. Consider an ordered product
`x_{θ₁}(f₁) ⋯ x_{θ_r}(f_r)` of root exponentials with distinct roots, `h`-positive and with
nondecreasing `h`-values. If all entries of the product lie in `Z`, then so do all parameters
`f_i`.

The proof uses the weight support of matrices: the entry at `(c, d)` of `x_{θ₁}(f₁) ⋯` with
`wt c = wt d + root θ₁` equals `f₁ (E_{θ₁})_{c d}`, because all other contributions move weights
by elements of `h`-level at least `h(θ₁)` different from `root θ₁`. Since the entries of `E_{θ₁}`
generate the unit ideal of `ℤ` (they are not all divisible by any prime), `f₁` is a
`ℤ`-linear combination of entries of the product. Then peel off `x_{θ₁}(f₁)` and recurse. -/

noncomputable section

universe u

open Matrix Finset

namespace Langlands.GroupScheme.SplitExistence

namespace LieRootData

variable {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y] {P : RootDatum J X Y}
  (D : LieRootData P) {S : Type*} [CommRing S]

/-- The matrix `A` moves weights only by elements of `W`: `A c d ≠ 0` implies
`wt c - wt d ∈ W`. -/
def Supp (A : Matrix (Fin D.n) (Fin D.n) S) (W : Set X) : Prop :=
  ∀ c d, A c d ≠ 0 → D.wt c - D.wt d ∈ W

variable {D} {A B : Matrix (Fin D.n) (Fin D.n) S} {W W₁ W₂ : Set X}

theorem supp_zero (W : Set X) : D.Supp (0 : Matrix (Fin D.n) (Fin D.n) S) W := by
  intro c d h
  simp at h

theorem Supp.mono (hA : D.Supp A W₁) (hW : W₁ ⊆ W₂) : D.Supp A W₂ :=
  fun c d h => hW (hA c d h)

theorem Supp.add (hA : D.Supp A W) (hB : D.Supp B W) : D.Supp (A + B) W := by
  intro c d h
  by_cases hc : A c d = 0
  · rw [Matrix.add_apply, hc, zero_add] at h
    exact hB c d h
  · exact hA c d hc

theorem Supp.smul (hA : D.Supp A W) (f : S) : D.Supp (f • A) W := by
  intro c d h
  rw [Matrix.smul_apply, smul_eq_mul] at h
  exact hA c d (right_ne_zero_of_mul h)

theorem Supp.mul (hA : D.Supp A W₁) (hB : D.Supp B W₂)
    (hW : ∀ x ∈ W₁, ∀ y ∈ W₂, x + y ∈ W) : D.Supp (A * B) W := by
  intro c d h
  rw [Matrix.mul_apply] at h
  obtain ⟨e, -, he⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  rw [← sub_add_sub_cancel (D.wt c) (D.wt e) (D.wt d)]
  exact hW _ (hA c e (left_ne_zero_of_mul he)) _ (hB e d (right_ne_zero_of_mul he))

theorem supp_sum {ι : Type*} (s : Finset ι) {F : ι → Matrix (Fin D.n) (Fin D.n) S}
    (hF : ∀ i ∈ s, D.Supp (F i) W) : D.Supp (∑ i ∈ s, F i) W :=
  Finset.sum_induction F (fun A => D.Supp A W) (fun _ _ hA hB => hA.add hB) (supp_zero W) hF

variable (D) in
theorem supp_em (k : J) (i : ℕ) : D.Supp (D.em S k i) {i • P.root k} := by
  intro c d h
  have h' : D.e k i c d ≠ 0 := by
    intro h0
    apply h
    simp [em, h0]
  exact sub_eq_iff_eq_add'.mpr (D.e_weight k i c d h')

/-- The root exponential as `1 + f E_k + Σ_{i < n} f^{i+2} e_k^{(i+2)}`. -/
theorem divExp_decomp (k : J) (f : S) :
    divExp (D.e k) f =
      1 + f • D.E S k + ∑ i ∈ range D.n, f ^ (i + 2) • D.em S k (i + 2) := by
  have hext : divExp (D.e k) f = ∑ i ∈ range (D.n + 2), f ^ i • D.em S k i := by
    rw [divExp_eq, Finset.sum_range_succ _ (D.n + 1), D.em_eq_zero k (Nat.lt_succ_self D.n),
      smul_zero, add_zero]
  rw [hext, Finset.sum_range_succ', Finset.sum_range_succ', pow_zero, D.em_zero, one_smul,
    pow_one]
  abel

variable (h : X →+ ℤ)

theorem supp_tail (k : J) (hk : 0 < h (P.root k)) (f : S) :
    D.Supp (∑ i ∈ range D.n, f ^ (i + 2) • D.em S k (i + 2)) {x | 2 * h (P.root k) ≤ h x} := by
  refine supp_sum _ fun i _ => ((D.supp_em k (i + 2)).smul _).mono ?_
  rintro x rfl
  simp only [Set.mem_ofPred_eq, map_nsmul, nsmul_eq_mul]
  push_cast
  nlinarith

variable (P) in
/-- The weight differences of `h`-level at least `h(root ε)` other than `root ε`. -/
def bigSet (ε : J) : Set X :=
  {x | h (P.root ε) ≤ h x ∧ x ≠ P.root ε}

theorem mem_bigSet_of_lt {ε : J} {x : X} (hx : h (P.root ε) < h x) : x ∈ bigSet P h ε :=
  ⟨hx.le, fun he => by rw [he] at hx; exact lt_irrefl _ hx⟩

theorem add_mem_bigSet {ε : J} (hε : 0 < h (P.root ε)) {x y : X} (hx : x ∈ bigSet P h ε)
    (hy : y ∈ bigSet P h ε) : x + y ∈ bigSet P h ε := by
  apply mem_bigSet_of_lt
  rw [map_add]
  linarith [hx.1, hy.1]

/-- A root exponential of a root `θ ≠ ε` with `h(θ) ≥ h(ε) > 0` differs from `1` by a matrix
supported in `bigSet P h ε`. -/
theorem supp_divExp_sub_one {ε θ : J} (hε : 0 < h (P.root ε)) (hθε : ε ≠ θ)
    (hle : h (P.root ε) ≤ h (P.root θ)) (f : S) :
    D.Supp (divExp (D.e θ) f - 1) (bigSet P h ε) := by
  rw [divExp_decomp, add_assoc, add_sub_cancel_left]
  refine Supp.add ?_ ?_
  · refine ((D.supp_em θ 1).smul f).mono ?_
    rintro x rfl
    rw [one_smul]
    exact ⟨hle, fun he => hθε (P.root.injective he).symm⟩
  · refine (supp_tail h θ (by linarith) f).mono fun x hx => mem_bigSet_of_lt h ?_
    simp only [Set.mem_ofPred_eq] at hx
    linarith

/-- An ordered product of root exponentials of roots `θ ≠ ε` with `h(θ) ≥ h(ε) > 0` differs
from `1` by a matrix supported in `bigSet P h ε`. -/
theorem supp_prod_sub_one {ε : J} (hε : 0 < h (P.root ε)) :
    ∀ L : List (J × S), (∀ q ∈ L, ε ≠ q.1 ∧ h (P.root ε) ≤ h (P.root q.1)) →
      D.Supp ((L.map fun p => divExp (D.e p.1) p.2).prod - 1) (bigSet P h ε) := by
  intro L
  induction L with
  | nil =>
    intro _
    simpa using supp_zero (D := D) (S := S) (bigSet P h ε)
  | cons q L ih =>
    intro hL
    have hq := hL q (List.mem_cons_self ..)
    have hL' := ih fun q' hq' => hL q' (List.mem_cons_of_mem _ hq')
    have hx := D.supp_divExp_sub_one h hε hq.1 hq.2 q.2
    rw [List.map_cons, List.prod_cons]
    have hdec : divExp (D.e q.1) q.2 * (L.map fun p => divExp (D.e p.1) p.2).prod - 1 =
        (divExp (D.e q.1) q.2 - 1) * ((L.map fun p => divExp (D.e p.1) p.2).prod - 1) +
          (divExp (D.e q.1) q.2 - 1) + ((L.map fun p => divExp (D.e p.1) p.2).prod - 1) := by
      noncomm_ring
    rw [hdec]
    exact ((hx.mul hL' fun x hx y hy => add_mem_bigSet h hε hx hy).add hx).add hL'

/-- The entry of `x_ε(f) x_{θ₂}(f₂) ⋯` at `(c, d)` with `wt c = wt d + root ε` is
`f (E_ε)_{c d}`. -/
theorem prod_cons_apply {ε : J} (hε : 0 < h (P.root ε)) (f : S) (L : List (J × S))
    (hL : ∀ q ∈ L, ε ≠ q.1 ∧ h (P.root ε) ≤ h (P.root q.1)) {c d : Fin D.n}
    (hcd : D.wt c = D.wt d + P.root ε) :
    (divExp (D.e ε) f * (L.map fun p => divExp (D.e p.1) p.2).prod) c d = f * D.E S ε c d := by
  set Q := (L.map fun p => divExp (D.e p.1) p.2).prod
  have hQ := D.supp_prod_sub_one h hε L hL
  have hdec : divExp (D.e ε) f * Q - 1 - f • D.E S ε =
      (divExp (D.e ε) f - 1 - f • D.E S ε) + (divExp (D.e ε) f - 1) * (Q - 1) + (Q - 1) := by
    noncomm_ring
  have hlev : ∀ x ∈ ({P.root ε} : Set X), h (P.root ε) ≤ h x := by
    rintro x rfl
    exact le_rfl
  have h1 : D.Supp (divExp (D.e ε) f - 1 - f • D.E S ε) (bigSet P h ε) := by
    rw [divExp_decomp, add_assoc, add_sub_cancel_left, add_sub_cancel_left]
    refine (supp_tail h ε hε f).mono fun x hx => mem_bigSet_of_lt h ?_
    simp only [Set.mem_ofPred_eq] at hx
    linarith
  have h2 : D.Supp (divExp (D.e ε) f - 1) {x | h (P.root ε) ≤ h x} := by
    rw [divExp_decomp, add_assoc, add_sub_cancel_left]
    refine Supp.add (((D.supp_em ε 1).smul f).mono ?_) ((supp_tail h ε hε f).mono ?_)
    · rintro x rfl
      simp
    · intro x hx
      simp only [Set.mem_ofPred_eq] at hx ⊢
      linarith
  have hsupp : D.Supp (divExp (D.e ε) f * Q - 1 - f • D.E S ε) (bigSet P h ε) := by
    rw [hdec]
    refine (h1.add (h2.mul hQ fun x hx y hy => mem_bigSet_of_lt h ?_)).add hQ
    simp only [Set.mem_ofPred_eq] at hx
    rw [map_add]
    linarith [hy.1]
  have hne : c ≠ d := by
    rintro rfl
    have := congrArg h hcd
    rw [map_add] at this
    linarith
  by_contra hcon
  have := hsupp c d (by
    rw [Matrix.sub_apply, Matrix.sub_apply, Matrix.one_apply_ne hne, sub_zero, Matrix.smul_apply,
      smul_eq_mul]
    exact sub_ne_zero.mpr hcon)
  rw [hcd, add_sub_cancel_left] at this
  exact this.2 rfl

variable (D) in
/-- The entries of `E_k` generate the unit ideal of `ℤ`. -/
theorem exists_int_sum_eq_one (k : J) :
    ∃ a : Fin D.n → Fin D.n → ℤ, ∑ c, ∑ d, a c d * D.e k 1 c d = 1 := by
  classical
  set v : Fin D.n × Fin D.n → ℤ := fun p => D.e k 1 p.1 p.2 with hv
  have h1 : (1 : ℤ) ∈ Ideal.span (Set.range v) := by
    by_contra hI
    set I := Ideal.span (Set.range v)
    obtain ⟨g, hg⟩ : ∃ g : ℤ, I = Ideal.span {g} :=
      ⟨Submodule.IsPrincipal.generator I, (Ideal.span_singleton_generator I).symm⟩
    have hg1 : g.natAbs ≠ 1 := by
      intro hg1
      apply hI
      rw [hg, Ideal.mem_span_singleton, ← Int.natAbs_dvd_natAbs, hg1]
      simp
    obtain ⟨p, hp, hpg⟩ := Int.exists_prime_and_dvd hg1
    apply D.e_one_map_ne_zero k p.natAbs (Int.prime_iff_natAbs_prime.mp hp)
    ext c d
    simp only [Matrix.map_apply, eq_intCast, Matrix.zero_apply]
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hmem : D.e k 1 c d ∈ I := Ideal.subset_span ⟨(c, d), rfl⟩
    rw [hg, Ideal.mem_span_singleton] at hmem
    exact Int.natAbs_dvd.mpr (hpg.trans hmem)
  obtain ⟨a, ha⟩ := Ideal.mem_span_range_iff_exists_fun.mp h1
  refine ⟨fun c d => a (c, d), ?_⟩
  rw [← ha, Fintype.sum_prod_type]

theorem mul_mem_apply (Z : Subring S) (hA : ∀ c d, A c d ∈ Z) (hB : ∀ c d, B c d ∈ Z)
    (c d : Fin D.n) : (A * B) c d ∈ Z := by
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun e _ => Subring.mul_mem _ (hA c e) (hB e d)

theorem divExp_mem_apply (Z : Subring S) (k : J) {f : S} (hf : f ∈ Z) (c d : Fin D.n) :
    divExp (D.e k) f c d ∈ Z := by
  rw [divExp_eq, Matrix.sum_apply]
  refine Subring.sum_mem _ fun i _ => ?_
  rw [Matrix.smul_apply, smul_eq_mul]
  refine Subring.mul_mem _ (Subring.pow_mem _ hf _) ?_
  simp only [em, Matrix.map_apply, eq_intCast]
  exact intCast_mem _ _

/-- **Integrality peeling.** If an ordered product of root exponentials (distinct roots,
`h`-positive, nondecreasing `h`-values) has all entries in a subring `Z`, then all its
parameters lie in `Z`. -/
theorem mem_of_prod_mem (Z : Subring S) : ∀ L : List (J × S), (∀ p ∈ L, 0 < h (P.root p.1)) →
    L.Pairwise (fun p q => p.1 ≠ q.1 ∧ h (P.root p.1) ≤ h (P.root q.1)) →
    (∀ c d, (L.map fun p => divExp (D.e p.1) p.2).prod c d ∈ Z) → ∀ p ∈ L, p.2 ∈ Z := by
  intro L
  induction L with
  | nil => simp
  | cons p L ih =>
    obtain ⟨ε, f⟩ := p
    intro hpos hpw hZ
    rw [List.pairwise_cons] at hpw
    have hεpos : 0 < h (P.root ε) := hpos _ (List.mem_cons_self ..)
    have hL : ∀ q ∈ L, ε ≠ q.1 ∧ h (P.root ε) ≤ h (P.root q.1) := hpw.1
    rw [List.map_cons, List.prod_cons] at hZ
    have hf : f ∈ Z := by
      obtain ⟨a, ha⟩ := D.exists_int_sum_eq_one ε
      have ha' := congrArg (Int.cast : ℤ → S) ha
      push_cast at ha'
      have hsum : ∑ c, ∑ d, (a c d : S) * (f * D.E S ε c d) = f := by
        calc ∑ c, ∑ d, (a c d : S) * (f * D.E S ε c d)
            = f * ∑ c, ∑ d, (a c d : S) * (D.e ε 1 c d : S) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun c _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun d _ => ?_
              simp only [E, em, Matrix.map_apply, eq_intCast]
              ring
          _ = f := by rw [ha', mul_one]
      rw [← hsum]
      refine Subring.sum_mem _ fun c _ => Subring.sum_mem _ fun d _ =>
        Subring.mul_mem _ (intCast_mem _ _) ?_
      by_cases he : D.e ε 1 c d = 0
      · simp [E, em, he]
      · have hw := D.e_weight ε 1 c d he
        rw [one_smul] at hw
        rw [← D.prod_cons_apply h hεpos f L hL hw]
        exact hZ c d
    have hZ₁ : ∀ c d, (L.map fun p => divExp (D.e p.1) p.2).prod c d ∈ Z := by
      have hprod : (L.map fun p => divExp (D.e p.1) p.2).prod =
          divExp (D.e ε) (-f) * (divExp (D.e ε) f * (L.map fun p => divExp (D.e p.1) p.2).prod) := by
        rw [← Matrix.mul_assoc, D.divExp_neg_mul_divExp, Matrix.one_mul]
      rw [hprod]
      exact mul_mem_apply Z (divExp_mem_apply Z ε (Subring.neg_mem _ hf)) hZ
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hf
    · exact ih (fun p hp => hpos p (List.mem_cons_of_mem _ hp)) hpw.2 hZ₁ q hq

end LieRootData

end Langlands.GroupScheme.SplitExistence
