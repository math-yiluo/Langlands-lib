import Langlands.Group.GL.UpperBruhatBoundaryStatement
import Langlands.Group.GL.UpperBruhatRankProof
import Langlands.Group.GL.UpperBruhatLocalClosednessProof
import Mathlib.Topology.Instances.Matrix

/-! Boundary points of actual upper Bruhat cells lie in cells with fewer inversions. -/

namespace Langlands.GeneralLinear

universe u

namespace UpperBruhatBoundary

section Profile

variable {n : ℕ}

/-- The number of columns `c < j` whose image `w c` is at least `i`. -/
def profile (w : Equiv.Perm (Fin n)) (i j : ℕ) : ℕ :=
  ∑ c : Fin n, if c.val < j ∧ i ≤ (w c).val then 1 else 0

/-- The published column count is the profile at the same endpoints. -/
theorem count_eq_profile (w : Equiv.Perm (Fin n)) (i : Fin (n + 1)) (k : ℕ) :
    UpperBruhatRank.count w i k = profile w i.val k := by
  rw [UpperBruhatRank.count, Finset.card_filter]
  rfl

/-- A pointwise inequality with one extra unit at `a` gives a strict inequality of sums. -/
theorem sum_add_one_le {f g : Fin n → ℕ} (a : Fin n)
    (h : ∀ c, f c + (if c = a then 1 else 0) ≤ g c) :
    (∑ c, f c) + 1 ≤ ∑ c, g c := by
  have h1 : (∑ c : Fin n, if c = a then 1 else 0) = 1 := by simp
  calc (∑ c, f c) + 1 = ∑ c, (f c + if c = a then 1 else 0) := by
        rw [Finset.sum_add_distrib, h1]
    _ ≤ ∑ c, g c := Finset.sum_le_sum fun c _ => h c

/-- Precomposing with a transposition changes a sum of `f c (v c)` only at the two
transposed indices. -/
theorem sum_comp_swap (f : Fin n → Fin n → ℕ) (v : Equiv.Perm (Fin n)) {a b : Fin n}
    (hab : a ≠ b) :
    (∑ c, f c (v (Equiv.swap a b c))) + f a (v a) + f b (v b) =
      (∑ c, f c (v c)) + f a (v b) + f b (v a) := by
  classical
  have hb : b ∈ (Finset.univ : Finset (Fin n)).erase a :=
    Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ b⟩
  rw [← Finset.add_sum_erase Finset.univ (fun c => f c (v (Equiv.swap a b c)))
      (Finset.mem_univ a),
    ← Finset.add_sum_erase _ (fun c => f c (v (Equiv.swap a b c))) hb,
    ← Finset.add_sum_erase Finset.univ (fun c => f c (v c)) (Finset.mem_univ a),
    ← Finset.add_sum_erase _ (fun c => f c (v c)) hb]
  have hrest : ∑ c ∈ (Finset.univ.erase a).erase b, f c (v (Equiv.swap a b c)) =
      ∑ c ∈ (Finset.univ.erase a).erase b, f c (v c) := by
    apply Finset.sum_congr rfl
    intro c hc
    have hcb := Finset.ne_of_mem_erase hc
    have hca := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hc)
    rw [Equiv.swap_apply_of_ne_of_ne hca hcb]
  simp only [hrest, Equiv.swap_apply_left, Equiv.swap_apply_right]
  ring

/-- Swapping two positions `a < b` with `v a < v b` raises the profile by at most one,
and only on the rectangle `a < j ≤ b`, `v a < i ≤ v b`. -/
theorem profile_mul_swap_le (v : Equiv.Perm (Fin n)) {a b : Fin n} (hab : a < b)
    (hv : v a < v b) (i j : ℕ) :
    profile (v * Equiv.swap a b) i j ≤ profile v i j +
      if a.val < j ∧ j ≤ b.val ∧ (v a).val < i ∧ i ≤ (v b).val then 1 else 0 := by
  have h := sum_comp_swap (fun c x : Fin n => if c.val < j ∧ i ≤ x.val then 1 else 0) v
    (ne_of_lt hab)
  have hab' : a.val < b.val := hab
  have hv' : (v a).val < (v b).val := hv
  have e1 : profile (v * Equiv.swap a b) i j =
      ∑ c : Fin n, if c.val < j ∧ i ≤ (v (Equiv.swap a b c)).val then 1 else 0 := rfl
  have e2 : profile v i j = ∑ c : Fin n, if c.val < j ∧ i ≤ (v c).val then 1 else 0 := rfl
  rw [e1, e2]
  split_ifs at h ⊢ <;> omega

/-- Swapping two positions `a < b` with `v a < v b` strictly increases the inversion count. -/
theorem permutationInversionCount_lt_mul_swap (v : Equiv.Perm (Fin n)) {a b : Fin n}
    (hab : a < b) (hv : v a < v b) :
    permutationInversionCount n v < permutationInversionCount n (v * Equiv.swap a b) := by
  classical
  rw [permutationInversionCount_eq_card_permutationInversions,
    permutationInversionCount_eq_card_permutationInversions]
  set t := Equiv.swap a b with ht
  have htt : ∀ x, t (t x) = x := fun x => Equiv.swap_apply_self a b x
  let ψ : Fin n × Fin n → Fin n × Fin n :=
    fun p => if t p.1 < t p.2 then (t p.1, t p.2) else p
  have hmem : (a, b) ∈ permutationInversions n (v * t) := by
    rw [mem_permutationInversions_iff]
    simp only [Equiv.Perm.mul_apply, ht, Equiv.swap_apply_left, Equiv.swap_apply_right]
    exact ⟨hab, hv⟩
  calc (permutationInversions n v).card
      ≤ ((permutationInversions n (v * t)).erase (a, b)).card := by
        apply Finset.card_le_card_of_injOn ψ
        · intro p hp
          rw [Finset.mem_coe, mem_permutationInversions_iff] at hp
          rw [Finset.mem_coe, Finset.mem_erase, mem_permutationInversions_iff]
          obtain ⟨p₁, p₂⟩ := p
          obtain ⟨hp1, hp2⟩ := hp
          simp only at hp1 hp2
          by_cases hlt : t p₁ < t p₂
          · simp only [ψ, ite_eq_left hlt, Equiv.Perm.mul_apply, htt]
            refine ⟨?_, hlt, hp2⟩
            intro he
            simp only [Prod.mk.injEq] at he
            have h1 : p₁ = b := by rw [← htt p₁, he.1, ht, Equiv.swap_apply_left]
            have h2 : p₂ = a := by rw [← htt p₂, he.2, ht, Equiv.swap_apply_right]
            rw [h1, h2] at hp1
            exact lt_asymm hab hp1
          · simp only [ψ, ite_eq_right hlt, Equiv.Perm.mul_apply]
            refine ⟨?_, hp1, ?_⟩
            · intro he
              simp only [Prod.mk.injEq] at he
              rw [he.1, he.2] at hp2
              exact lt_asymm hv hp2
            · -- `t` reverses the order of `p₁ < p₂`, so one of them is `a` or `b`.
              by_cases h1a : p₁ = a
              · rw [h1a] at hp1 hp2 hlt ⊢
                by_cases h2b : p₂ = b
                · rw [h2b] at hp2
                  exact absurd hv (lt_asymm hp2)
                · rw [ht, Equiv.swap_apply_left,
                    Equiv.swap_apply_of_ne_of_ne (ne_of_gt hp1) h2b]
                  exact hp2.trans hv
              · by_cases h1b : p₁ = b
                · rw [h1b] at hp1
                  exfalso
                  apply hlt
                  rw [h1b, ht, Equiv.swap_apply_right,
                    Equiv.swap_apply_of_ne_of_ne (ne_of_gt (hab.trans hp1)) (ne_of_gt hp1)]
                  exact hab.trans hp1
                · by_cases h2b : p₂ = b
                  · rw [h2b] at hp2 ⊢
                    rw [ht, Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne h1a h1b]
                    exact hv.trans hp2
                  · by_cases h2a : p₂ = a
                    · rw [h2a] at hp1
                      exfalso
                      apply hlt
                      rw [h2a, ht, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne h1a h1b]
                      exact hp1.trans hab
                    · exfalso
                      apply hlt
                      rw [ht, Equiv.swap_apply_of_ne_of_ne h1a h1b,
                        Equiv.swap_apply_of_ne_of_ne h2a h2b]
                      exact hp1
        · intro p hp q hq hpq
          rw [Finset.mem_coe, mem_permutationInversions_iff] at hp hq
          by_cases hp' : t p.1 < t p.2 <;> by_cases hq' : t q.1 < t q.2
          · simp only [ψ, ite_eq_left hp', ite_eq_left hq', Prod.mk.injEq] at hpq
            exact Prod.ext (t.injective hpq.1) (t.injective hpq.2)
          · simp only [ψ, ite_eq_left hp', ite_eq_right hq'] at hpq
            exfalso
            apply hq'
            rw [← hpq, htt, htt]
            exact hp.1
          · simp only [ψ, ite_eq_right hp', ite_eq_left hq'] at hpq
            exfalso
            apply hp'
            rw [hpq, htt, htt]
            exact hq.1
          · simpa only [ψ, ite_eq_right hp', ite_eq_right hq'] using hpq
    _ < (permutationInversions n (v * t)).card := Finset.card_erase_lt_of_mem hmem

/-- The inversion count is at most `n * n`. -/
theorem permutationInversionCount_le (v : Equiv.Perm (Fin n)) :
    permutationInversionCount n v ≤ n * n := by
  rw [permutationInversionCount_eq_card_permutationInversions]
  calc (permutationInversions n v).card ≤ Fintype.card (Fin n × Fin n) :=
        Finset.card_le_univ _
    _ = n * n := by simp

/-- In the rectangle where the swap can raise the profile, the profile of `w` has room:
here `a` is the first position where `v` and `w` differ and `b` is the first position
after `a` with `v a < v b ≤ w a`. -/
theorem profile_add_one_le (v w : Equiv.Perm (Fin n)) {a b : Fin n} {i j : ℕ}
    (hlow : ∀ c : Fin n, c.val < a.val → (v c).val = (w c).val)
    (hb : (v b).val ≤ (w a).val)
    (hmin : ∀ c : Fin n, a.val < c.val → c.val < b.val →
      (v c).val ≤ (v a).val ∨ (w a).val < (v c).val)
    (hle : profile v ((w a).val + 1) j ≤ profile w ((w a).val + 1) j)
    (hj : a.val < j) (hjb : j ≤ b.val) (hi : (v a).val < i) (hib : i ≤ (v b).val) :
    profile v i j + 1 ≤ profile w i j := by
  have key : profile v i j + profile w ((w a).val + 1) j + 1 ≤
      profile w i j + profile v ((w a).val + 1) j := by
    have h := sum_add_one_le
      (f := fun c => (if c.val < j ∧ i ≤ (v c).val then 1 else 0) +
        (if c.val < j ∧ (w a).val + 1 ≤ (w c).val then 1 else 0))
      (g := fun c => (if c.val < j ∧ i ≤ (w c).val then 1 else 0) +
        (if c.val < j ∧ (w a).val + 1 ≤ (v c).val then 1 else 0)) a ?_
    · simp only [Finset.sum_add_distrib] at h
      exact h
    · intro c
      rcases lt_trichotomy c a with hca | hca | hca
      · have hca' : c.val < a.val := hca
        have := hlow c hca'
        rw [ite_eq_right hca.ne]
        split_ifs <;> omega
      · rw [ite_eq_left hca, hca]
        split_ifs <;> omega
      · have hca' : a.val < c.val := hca
        rw [ite_eq_right hca.ne']
        by_cases hcj : c.val < j
        · have := hmin c hca' (by omega)
          split_ifs <;> omega
        · split_ifs <;> omega
  omega

/-- If `v ≠ w` and the profile of `v` is everywhere at most that of `w`, then some swap
of an increasing pair of positions of `v` keeps the profile at most that of `w`. -/
theorem exists_swap_step {v w : Equiv.Perm (Fin n)} (hvw : v ≠ w)
    (hle : ∀ i j, i ≤ n → j ≤ n → profile v i j ≤ profile w i j) :
    ∃ a b : Fin n, a < b ∧ v a < v b ∧
      ∀ i j, i ≤ n → j ≤ n → profile (v * Equiv.swap a b) i j ≤ profile w i j := by
  classical
  -- The first position `a` where `v` and `w` differ.
  let S := Finset.univ.filter fun c : Fin n => v c ≠ w c
  have hS : S.Nonempty := by
    obtain ⟨c, hc⟩ : ∃ c, v c ≠ w c := by
      by_contra h
      push Not at h
      exact hvw (Equiv.ext h)
    exact ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_univ c, hc⟩⟩
  obtain ⟨a, ha_mem, ha_min⟩ : ∃ a ∈ S, ∀ c ∈ S, a ≤ c :=
    ⟨S.min' hS, S.min'_mem hS, fun c hc => S.min'_le c hc⟩
  have ha : v a ≠ w a := (Finset.mem_filter.mp ha_mem).2
  have hlow : ∀ c : Fin n, c < a → v c = w c := by
    intro c hc
    by_contra h
    exact absurd (ha_min c (Finset.mem_filter.mpr ⟨Finset.mem_univ c, h⟩)) (not_le.mpr hc)
  have hlow' : ∀ c : Fin n, c.val < a.val → (v c).val = (w c).val :=
    fun c hc => congrArg Fin.val (hlow c hc)
  -- At the first difference, `v a < w a`.
  have hvwa : (v a).val < (w a).val := by
    rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne ha) with h | h
    · exact h
    · exfalso
      have key : profile w (v a).val (a.val + 1) + 1 ≤ profile v (v a).val (a.val + 1) := by
        apply sum_add_one_le a
        intro c
        rcases lt_trichotomy c a with hca | hca | hca
        · have hca' : c.val < a.val := hca
          have := hlow' c hca'
          rw [ite_eq_right hca.ne]
          split_ifs <;> omega
        · rw [ite_eq_left hca, hca]
          split_ifs <;> omega
        · have hca' : a.val < c.val := hca
          rw [ite_eq_right hca.ne']
          split_ifs <;> omega
      have := hle (v a).val (a.val + 1) (v a).isLt.le a.isLt
      omega
  -- The first position `b` after `a` with `v a < v b ≤ w a`.
  let T := Finset.univ.filter fun c : Fin n =>
    a < c ∧ (v a).val < (v c).val ∧ (v c).val ≤ (w a).val
  have hT : T.Nonempty := by
    refine ⟨v.symm (w a), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_, ?_, ?_⟩⟩
    · rcases lt_trichotomy (v.symm (w a)) a with h | h | h
      · exfalso
        have h' := hlow _ h
        rw [Equiv.apply_symm_apply] at h'
        have h'' := w.injective h'
        rw [← h''] at h
        exact lt_irrefl _ h
      · exfalso
        have h' := congrArg v h
        rw [Equiv.apply_symm_apply] at h'
        exact ha h'.symm
      · exact h
    · rw [Equiv.apply_symm_apply]
      exact hvwa
    · rw [Equiv.apply_symm_apply]
  obtain ⟨b, hb_mem, hb_min⟩ : ∃ b ∈ T, ∀ c ∈ T, b ≤ c :=
    ⟨T.min' hT, T.min'_mem hT, fun c hc => T.min'_le c hc⟩
  obtain ⟨hab, hvab, hvbw⟩ := (Finset.mem_filter.mp hb_mem).2
  have hmin : ∀ c : Fin n, a.val < c.val → c.val < b.val →
      (v c).val ≤ (v a).val ∨ (w a).val < (v c).val := by
    intro c hac hcb
    by_contra h
    push Not at h
    exact absurd (hb_min c (Finset.mem_filter.mpr ⟨Finset.mem_univ c, hac, h.1, h.2⟩))
      (not_le.mpr hcb)
  refine ⟨a, b, hab, hvab, ?_⟩
  intro i j hi hj
  have hswap := profile_mul_swap_le v hab hvab i j
  have hvw' := hle i j hi hj
  by_cases hr : a.val < j ∧ j ≤ b.val ∧ (v a).val < i ∧ i ≤ (v b).val
  · rw [ite_eq_left hr] at hswap
    have := profile_add_one_le v w hlow' hvbw hmin
      (hle ((w a).val + 1) j (w a).isLt hj) hr.1 hr.2.1 hr.2.2.1 hr.2.2.2
    omega
  · rw [ite_eq_right hr] at hswap
    omega

/-- Strong induction on `n * n - inv v`: each swap step strictly raises the inversion
count while keeping the profile below that of `w`. -/
theorem inversionCount_lt_of_profile_le (w : Equiv.Perm (Fin n)) :
    ∀ (k : ℕ) (v : Equiv.Perm (Fin n)), n * n - permutationInversionCount n v = k →
      v ≠ w → (∀ i j, i ≤ n → j ≤ n → profile v i j ≤ profile w i j) →
      permutationInversionCount n v < permutationInversionCount n w := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro v hk hvw hle
    obtain ⟨a, b, hab, hv, hle'⟩ := exists_swap_step hvw hle
    have hlt := permutationInversionCount_lt_mul_swap v hab hv
    by_cases heq : v * Equiv.swap a b = w
    · rw [← heq]
      exact hlt
    · have hbound := permutationInversionCount_le (v * Equiv.swap a b)
      exact hlt.trans (ih _ (by omega) _ rfl heq hle')

end Profile

/-- Distinct permutations ordered by all lower-left column counts have strictly
increasing inversion counts. -/
theorem rankOrderInversion : ∀ (n : ℕ) (v w : Equiv.Perm (Fin n)), v ≠ w →
    (∀ i j : Fin (n + 1), UpperBruhatRank.count v i j.val ≤ UpperBruhatRank.count w i j.val) →
    permutationInversionCount n v < permutationInversionCount n w := by
  intro n v w hvw hcount
  refine inversionCount_lt_of_profile_le w _ v rfl hvw ?_
  intro i j hi hj
  have := hcount ⟨i, by omega⟩ ⟨j, by omega⟩
  rwa [count_eq_profile, count_eq_profile] at this

end UpperBruhatBoundary

section RankTopology

variable {K : Type u} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [T2Space K] {n : ℕ}

open UpperBruhatRank in
private theorem rank_corner_le_of_mem_closure (w : Equiv.Perm (Fin n))
    {g : Langlands.GeneralLinear n K} (hg : g ∈ closure (upperBruhatCell n K w))
    (i j : Fin (n + 1)) :
    (corner i j (g : Matrix (Fin n) (Fin n) K)).rank ≤
      (corner i j (permutation n K w : Matrix (Fin n) (Fin n) K)).rank := by
  have hclosed : IsClosed {g : Langlands.GeneralLinear n K |
      (corner i j (g : Matrix (Fin n) (Fin n) K)).rank ≤
        (corner i j (permutation n K w : Matrix (Fin n) (Fin n) K)).rank} :=
    (isClosed_matrix_rank_le _).preimage (continuous_lowerLeftCorner i j)
  apply closure_minimal ?_ hclosed hg
  intro a ha
  exact ((upperBruhatRankCharacterization K n w a).mp ha i j).le

end RankTopology

/-- The boundary statement from the finite comparison of column counts with inversion
counts; the comparison is supplied by `UpperBruhatBoundary.rankOrderInversion`. -/
theorem upperBruhatBoundary_of_rankOrder
    (horder : ∀ (n : ℕ) (v w : Equiv.Perm (Fin n)), v ≠ w →
      (∀ i j : Fin (n + 1), UpperBruhatRank.count v i j.val ≤
        UpperBruhatRank.count w i j.val) →
      permutationInversionCount n v < permutationInversionCount n w) :
    UpperBruhatBoundaryStatement.{u} := by
  intro K _ _ _ _ n w g hg
  obtain ⟨a, b, v, ha, hb, hfact⟩ := fieldUpperBruhatFactorizationTheorem K n g
  have hgv : g ∈ upperBruhatCell n K v :=
    ⟨a, (mem_upperTriangularSubgroup_iff a).mpr ha,
      b, (mem_upperTriangularSubgroup_iff b).mpr hb, hfact⟩
  have hne : v ≠ w := by
    rintro rfl
    exact hg.2 hgv
  refine ⟨v, horder n v w hne ?_, hgv⟩
  intro i j
  have hle := rank_corner_le_of_mem_closure w hg.1 i j
  have heq := (upperBruhatRankCharacterization K n v g).mp hgv i j
  change (UpperBruhatRank.corner i j (g : Matrix (Fin n) (Fin n) K)).rank =
    (UpperBruhatRank.corner i j (permutation n K v : Matrix (Fin n) (Fin n) K)).rank at heq
  rw [heq, UpperBruhatRank.rank_corner_permutation,
    UpperBruhatRank.rank_corner_permutation] at hle
  exact hle

/-- Every point of the closure of an actual upper Bruhat cell outside the cell lies in an
actual cell whose permutation has strictly fewer inversions. -/
theorem upperBruhatBoundary : UpperBruhatBoundaryStatement.{u} :=
  upperBruhatBoundary_of_rankOrder UpperBruhatBoundary.rankOrderInversion

end Langlands.GeneralLinear
