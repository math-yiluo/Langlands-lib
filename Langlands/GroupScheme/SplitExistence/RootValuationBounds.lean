import Langlands.GroupScheme.SplitExistence.ClosedOrderedProduct
import Langlands.GroupScheme.SplitExistence.RootSubgroupRepresentation
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Basic.Real.Basic

/-! # Valuation bounds for root elements of a Chevalley group

Let `v` be an additive valuation of a commutative ring `K` and `θ : X →+ ℝ`. A matrix `M` over
`K` is `θ`-bounded if `v (M c d) ≥ θ(wt c - wt d)` for all basis vectors `c, d`. The bounded
matrices form a multiplicative monoid, and `x_j(s)` is bounded once `v s ≥ θ(j)`. Conversely, if
an ordered product `∏ x_γ(c_γ)` over distinct roots, listed in order of increasing positive
height, is bounded, then every coefficient satisfies `v (c_γ) ≥ θ(γ)`. -/

noncomputable section

universe u

open Matrix

namespace Langlands.GroupScheme.SplitExistence

namespace ChevalleyData

variable {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y] {P : RootDatum J X Y} {b : P.Base}
  (D : ChevalleyData P b) {K : Type u} [CommRing K] (v : AddValuation K (WithTop ℝ))

omit [AddCommGroup X] [AddCommGroup Y] in
theorem valuation_natCast_nonneg (n : ℕ) : 0 ≤ v (n : K) := by
  induction n with
  | zero => rw [Nat.cast_zero, v.map_zero]; exact le_top
  | succ n ih => rw [Nat.cast_succ]; exact v.map_le_add ih (by rw [v.map_one])

omit [AddCommGroup X] [AddCommGroup Y] in
theorem valuation_intCast_nonneg (z : ℤ) : 0 ≤ v (z : K) := by
  cases z with
  | ofNat n => rw [Int.ofNat_eq_natCast, Int.cast_natCast]; exact valuation_natCast_nonneg v n
  | negSucc n => rw [Int.cast_negSucc, v.map_neg]; exact valuation_natCast_nonneg v _

/-- If every entry of `s e_j(1)` has valuation at least `t`, then so does `s`: the entries of
`e_j(1)` generate the unit ideal of `ℤ`. -/
theorem le_of_forall_le_mul_e_one (j : J) {t : WithTop ℝ} {s : K}
    (hs : ∀ c d, t ≤ v (s * (D.e j 1 c d : K))) : t ≤ v s := by
  let I : Ideal ℤ :=
    { carrier := {z | t ≤ v (s * (z : K))}
      add_mem' := fun {z z'} hz hz' => by
        simp only [Set.mem_ofPred_eq, Int.cast_add, mul_add] at hz hz' ⊢
        exact v.map_le_add hz hz'
      zero_mem' := by
        simp only [Set.mem_ofPred_eq, Int.cast_zero, mul_zero, v.map_zero]
        exact le_top
      smul_mem' := fun n z hz => by
        simp only [Set.mem_ofPred_eq, smul_eq_mul, Int.cast_mul] at hz ⊢
        rw [mul_left_comm, v.map_mul]
        exact hz.trans (le_add_of_nonneg_left (valuation_intCast_nonneg v n)) }
  have hle : Ideal.span (Set.range fun cd : Fin D.n × Fin D.n => D.e j 1 cd.1 cd.2) ≤ I := by
    rw [Ideal.span_le]
    rintro _ ⟨cd, rfl⟩
    exact hs cd.1 cd.2
  have h1 := hle (D.one_mem_span_e_one j)
  change t ≤ v (s * ((1 : ℤ) : K)) at h1
  rwa [Int.cast_one, mul_one] at h1

variable (θ : X →+ ℝ)

/-- A matrix is `θ`-bounded if its entry `(c, d)` has valuation at least `θ(wt c - wt d)`. -/
def NormBound (M : Matrix (Fin D.n) (Fin D.n) K) : Prop :=
  ∀ c d, ((θ (D.wt c - D.wt d) : ℝ) : WithTop ℝ) ≤ v (M c d)

theorem normBound_one : D.NormBound v θ (1 : Matrix (Fin D.n) (Fin D.n) K) := by
  intro c d
  by_cases hcd : c = d
  · subst hcd
    rw [sub_self, map_zero, Matrix.one_apply_eq, v.map_one, WithTop.coe_zero]
  · rw [Matrix.one_apply_ne hcd, v.map_zero]
    exact le_top

theorem normBound_mul {M N : Matrix (Fin D.n) (Fin D.n) K} (hM : D.NormBound v θ M)
    (hN : D.NormBound v θ N) : D.NormBound v θ (M * N) := by
  intro c d
  rw [Matrix.mul_apply]
  refine v.map_le_sum fun u _ => ?_
  rw [v.map_mul]
  have e : θ (D.wt c - D.wt d) = θ (D.wt c - D.wt u) + θ (D.wt u - D.wt d) := by
    rw [← map_add]
    congr 1
    abel
  rw [e, WithTop.coe_add]
  exact add_le_add (hM c u) (hN u d)

theorem divExp_apply (j : J) (s : K) (c d : Fin D.n) :
    divExp (D.e j) s c d = ∑ k ∈ Finset.range (D.n + 1), s ^ k * (D.e j k c d : K) := by
  simp [divExp, Matrix.sum_apply]

/-- `x_j(s)` is `θ`-bounded once `v s ≥ θ(j)`. -/
theorem normBound_divExp {j : J} {s : K} (hs : ((θ (P.root j) : ℝ) : WithTop ℝ) ≤ v s) :
    D.NormBound v θ (divExp (D.e j) s) := by
  intro c d
  rw [divExp_apply]
  refine v.map_le_sum fun k _ => ?_
  by_cases hk : D.e j k c d = 0
  · rw [hk, Int.cast_zero, mul_zero, v.map_zero]
    exact le_top
  · have hw := D.e_weight j k c d hk
    rw [v.map_mul, v.map_pow]
    have e : D.wt c - D.wt d = k • P.root j := by rw [hw]; abel
    rw [e, map_nsmul, WithTop.coe_nsmul]
    exact (nsmul_le_nsmul_right hs k).trans
      (le_add_of_nonneg_right (valuation_intCast_nonneg v _))

/-- The entries of `M - 1` lie over pairs of basis vectors whose weight difference is in `A`. -/
def ShiftSupport (A : Set X) (M : Matrix (Fin D.n) (Fin D.n) K) : Prop :=
  ∀ c d, M c d ≠ (1 : Matrix (Fin D.n) (Fin D.n) K) c d → D.wt c - D.wt d ∈ A

theorem shiftSupport_one (A : Set X) : D.ShiftSupport A (1 : Matrix (Fin D.n) (Fin D.n) K) :=
  fun _ _ h => absurd rfl h

theorem shiftSupport_mul {A : Set X} (hA : ∀ x ∈ A, ∀ y ∈ A, x + y ∈ A)
    {M N : Matrix (Fin D.n) (Fin D.n) K} (hM : D.ShiftSupport A M) (hN : D.ShiftSupport A N) :
    D.ShiftSupport A (M * N) := by
  intro c d hcd
  by_contra hA'
  apply hcd
  have hMcd : M c d = (1 : Matrix (Fin D.n) (Fin D.n) K) c d := by
    by_contra h'
    exact hA' (hM c d h')
  have hNcd : N c d = (1 : Matrix (Fin D.n) (Fin D.n) K) c d := by
    by_contra h'
    exact hA' (hN c d h')
  have e : M * N = M + N - 1 + (M - 1) * (N - 1) := by
    simp only [sub_mul, mul_sub, mul_one, one_mul]
    abel
  have hs : ∑ u, (M - 1) c u * (N - 1) u d = 0 := by
    refine Finset.sum_eq_zero fun u _ => ?_
    by_cases h1 : M c u = (1 : Matrix (Fin D.n) (Fin D.n) K) c u
    · rw [Matrix.sub_apply, h1, sub_self, zero_mul]
    · by_cases h2 : N u d = (1 : Matrix (Fin D.n) (Fin D.n) K) u d
      · rw [Matrix.sub_apply N, h2, sub_self, mul_zero]
      · exfalso
        apply hA'
        have := hA _ (hM c u h1) _ (hN u d h2)
        rwa [sub_add_sub_cancel] at this
  rw [e, Matrix.add_apply, Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply, hs, hMcd, hNcd]
  ring

/-- `x_j(s) - 1` lies over weight differences `k j` with `k ≥ 1`. -/
theorem shiftSupport_divExp {A : Set X} {j : J} (hA : ∀ k : ℕ, 1 ≤ k → k • P.root j ∈ A)
    (s : K) : D.ShiftSupport A (divExp (D.e j) s) := by
  intro c d hcd
  rw [divExp_apply, Finset.sum_range_succ', pow_zero, one_mul, D.e_zero] at hcd
  have hne : ∑ k ∈ Finset.range D.n, s ^ (k + 1) * (D.e j (k + 1) c d : K) ≠ 0 := by
    intro h0
    apply hcd
    rw [h0, zero_add, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  obtain ⟨k, -, hk⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have hk' : D.e j (k + 1) c d ≠ 0 := by
    intro h0
    apply hk
    rw [h0, Int.cast_zero, mul_zero]
  have hw := D.e_weight j (k + 1) c d hk'
  have e : D.wt c - D.wt d = (k + 1) • P.root j := by rw [hw]; abel
  rw [e]
  exact hA (k + 1) (by omega)

theorem shiftSupport_listProd {A : Set X} (hA : ∀ x ∈ A, ∀ y ∈ A, x + y ∈ A) (w : J → K) :
    ∀ l : List J, (∀ j ∈ l, ∀ k : ℕ, 1 ≤ k → k • P.root j ∈ A) →
      D.ShiftSupport A ((D.listProd l w : GL (Fin D.n) K) : Matrix (Fin D.n) (Fin D.n) K)
  | [], _ => by rw [listProd_nil, Units.val_one]; exact D.shiftSupport_one A
  | j :: l, hl => by
    rw [listProd_cons, Units.val_mul, coe_x]
    exact D.shiftSupport_mul hA (D.shiftSupport_divExp (hl j (List.mem_cons_self ..)) _)
      (shiftSupport_listProd hA w l fun i hi => hl i (List.mem_cons_of_mem _ hi))

/-- The entries of `x_j(s) N` over the weight difference `j`, when `N - 1` lies over weight
differences of height at least `h(j)` other than `j`. -/
theorem divExp_mul_apply_of_shiftSupport (h : X →+ ℤ) {j : J} (hj : 0 < h (P.root j))
    {A : Set X} (hAh : ∀ x ∈ A, h (P.root j) ≤ h x) (hjA : P.root j ∉ A)
    {N : Matrix (Fin D.n) (Fin D.n) K} (hN : D.ShiftSupport A N) (s : K) {c d : Fin D.n}
    (hcd : D.wt c - D.wt d = P.root j) :
    (divExp (D.e j) s * N) c d = s * (D.e j 1 c d : K) := by
  have hX : D.ShiftSupport {x | ∃ k : ℕ, 1 ≤ k ∧ x = k • P.root j} (divExp (D.e j) s) :=
    D.shiftSupport_divExp (A := {x | ∃ k : ℕ, 1 ≤ k ∧ x = k • P.root j})
      (fun k hk => ⟨k, hk, rfl⟩) s
  have hdd : N d d = 1 := by
    by_contra h'
    have h0 := hN d d (by rwa [Matrix.one_apply_eq])
    rw [sub_self] at h0
    have := hAh _ h0
    rw [map_zero] at this
    omega
  have hentry : divExp (D.e j) s c d = s * (D.e j 1 c d : K) := by
    rw [divExp_apply]
    have hn : 1 ∈ Finset.range (D.n + 1) := by
      have := c.pos
      rw [Finset.mem_range]
      omega
    rw [Finset.sum_eq_single_of_mem 1 hn, pow_one]
    intro k _ hk1
    by_cases hk : D.e j k c d = 0
    · rw [hk, Int.cast_zero, mul_zero]
    · exfalso
      have hw := D.e_weight j k c d hk
      have e : D.wt c - D.wt d = k • P.root j := by rw [hw]; abel
      rw [hcd] at e
      have := congrArg h e
      rw [map_nsmul, nsmul_eq_mul] at this
      have hk' : (k : ℤ) = 1 := by
        have h2 : (1 - (k : ℤ)) * h (P.root j) = 0 := by linarith
        rcases mul_eq_zero.1 h2 with h3 | h3
        · linarith
        · omega
      exact hk1 (by exact_mod_cast hk')
  rw [Matrix.mul_apply, Finset.sum_eq_single d, hentry, hdd, mul_one]
  · intro u _ hud
    by_cases hN0 : N u d = 0
    · rw [hN0, mul_zero]
    have hud' := hN u d (by rwa [Matrix.one_apply_ne hud])
    by_cases hcu : c = u
    · subst hcu
      exact absurd (hcd ▸ hud') hjA
    by_cases hX0 : divExp (D.e j) s c u = 0
    · rw [hX0, zero_mul]
    exfalso
    obtain ⟨k, hk, hck⟩ := hX c u (by rwa [Matrix.one_apply_ne hcu])
    have e1 : h (D.wt c - D.wt d) = h (D.wt c - D.wt u) + h (D.wt u - D.wt d) := by
      rw [← map_add]
      congr 1
      abel
    rw [hcd, hck, map_nsmul, nsmul_eq_mul] at e1
    have h1 := hAh _ hud'
    have hk' : (1 : ℤ) ≤ k := by exact_mod_cast hk
    nlinarith
  · intro hd
    exact absurd (Finset.mem_univ d) hd

/-- **Peeling.** If an ordered product `∏ x_γ(w_γ)` over distinct roots listed in order of
increasing positive height `h` is `θ`-bounded, then `v (w_γ) ≥ θ(γ)` for every `γ` in the
list. -/
theorem le_of_normBound_listProd (h : X →+ ℤ) :
    ∀ (l : List J), l.Nodup → l.Pairwise (fun i j => h (P.root i) ≤ h (P.root j)) →
      (∀ j ∈ l, 0 < h (P.root j)) → ∀ (w : J → K),
      D.NormBound v θ ((D.listProd l w : GL (Fin D.n) K) : Matrix (Fin D.n) (Fin D.n) K) →
      ∀ j ∈ l, ((θ (P.root j) : ℝ) : WithTop ℝ) ≤ v (w j)
  | [], _, _, _, _, _, j, hj => absurd hj List.not_mem_nil
  | γ :: l, hnd, hs, hpos, w, hb, j, hj => by
    rw [List.nodup_cons] at hnd
    rw [List.pairwise_cons] at hs
    have hγpos := hpos γ (List.mem_cons_self ..)
    have hγ : ((θ (P.root γ) : ℝ) : WithTop ℝ) ≤ v (w γ) := by
      set A : Set X := {x | h (P.root γ) < h x} ∪ {x | ∃ i ∈ l, x = P.root i} with hAdef
      have hAh : ∀ x ∈ A, h (P.root γ) ≤ h x := by
        rintro x (hx | ⟨i, hi, rfl⟩)
        · exact le_of_lt hx
        · exact hs.1 i hi
      have hγA : P.root γ ∉ A := by
        rintro (hx | ⟨i, hi, hi'⟩)
        · exact lt_irrefl _ (show h (P.root γ) < h (P.root γ) from hx)
        · exact hnd.1 (P.root.injective hi' ▸ hi)
      have hA : ∀ x ∈ A, ∀ y ∈ A, x + y ∈ A := by
        intro x hx y hy
        left
        have h1 := hAh x hx
        have h2 := hAh y hy
        show h (P.root γ) < h (x + y)
        rw [map_add]
        linarith
      have hN : D.ShiftSupport A
          ((D.listProd l w : GL (Fin D.n) K) : Matrix (Fin D.n) (Fin D.n) K) := by
        refine D.shiftSupport_listProd hA w l fun i hi k hk => ?_
        rcases eq_or_lt_of_le hk with rfl | hk2
        · right
          exact ⟨i, hi, one_nsmul _⟩
        · left
          show h (P.root γ) < h (k • P.root i)
          rw [map_nsmul, nsmul_eq_mul]
          have h1 := hs.1 i hi
          have hk' : (2 : ℤ) ≤ k := by exact_mod_cast hk2
          nlinarith
      refine D.le_of_forall_le_mul_e_one v γ fun c d => ?_
      by_cases hcd : D.wt c - D.wt d = P.root γ
      · have hbcd := hb c d
        rw [listProd_cons, Units.val_mul, coe_x,
          D.divExp_mul_apply_of_shiftSupport h hγpos hAh hγA hN _ hcd, hcd] at hbcd
        exact hbcd
      · have h0 : D.e γ 1 c d = 0 := by
          by_contra hne
          apply hcd
          rw [D.e_weight γ 1 c d hne, one_nsmul]
          abel
        rw [h0, Int.cast_zero, mul_zero, v.map_zero]
        exact le_top
    rcases List.mem_cons.1 hj with rfl | hjl
    · exact hγ
    · refine le_of_normBound_listProd h l hnd.2 hs.2
        (fun i hi => hpos i (List.mem_cons_of_mem _ hi)) w ?_ j hjl
      have e : ((D.listProd l w : GL (Fin D.n) K) : Matrix (Fin D.n) (Fin D.n) K) =
          (D.x γ (-w γ) : Matrix (Fin D.n) (Fin D.n) K) *
            ((D.listProd (γ :: l) w : GL (Fin D.n) K) : Matrix (Fin D.n) (Fin D.n) K) := by
        rw [listProd_cons, ← Units.val_mul, ← mul_assoc, ← x_add, neg_add_cancel, x_zero,
          one_mul]
      rw [e, coe_x]
      exact D.normBound_mul v θ (D.normBound_divExp v θ (by rwa [v.map_neg])) hb

end ChevalleyData

end Langlands.GroupScheme.SplitExistence
