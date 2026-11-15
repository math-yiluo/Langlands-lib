import Langlands.GroupScheme.Reductive.LocalSplitRootPairCommutator

/-! # The commutator of two simple root groups of type `A₂` -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.LinearAlgebra

section RankTwo

variable {I : Type*} {J : Type*} [Finite J] [DecidableEq J] {P : RootDatum J (I → ℤ) (I → ℤ)}
  [P.IsReduced]
  {b : P.Base} {a c : J}

omit [Finite J] [P.IsReduced] in
/-- The combination `p • a + q • c` of two distinct simple roots as a sum over the base. -/
theorem sum_pair_eq (ha : a ∈ b.support) (hc : c ∈ b.support) (hac : a ≠ c) (p q : ℤ) :
    ∑ j ∈ b.support, (if j = a then p else if j = c then q else 0) • P.root j =
      p • P.root a + q • P.root c := by
  have h : ∀ j, (if j = a then p else if j = c then q else 0) =
      (if j = a then p else 0) + (if j = c then q else 0) := by
    intro j
    by_cases hja : j = a
    · subst hja
      simp [hac]
    · simp [hja]
  simp only [h, add_smul, Finset.sum_add_distrib, ite_smul, zero_smul, Finset.sum_ite_eq',
    ha, hc, ↓reduceIte]

omit [Finite J] [P.IsReduced] in
/-- The combination `p • a + q • c - j` of two distinct simple roots and a third simple root
as a sum over the base. -/
theorem sum_pair_sub_eq (ha : a ∈ b.support) (hc : c ∈ b.support) (hac : a ≠ c) {j : J}
    (hj : j ∈ b.support) (hja : j ≠ a) (hjc : j ≠ c) (p q : ℤ) :
    ∑ t ∈ b.support,
        (if t = a then p else if t = c then q else if t = j then -1 else 0) • P.root t =
      p • P.root a + q • P.root c - P.root j := by
  have h : ∀ t, (if t = a then p else if t = c then q else if t = j then (-1 : ℤ) else 0) =
      (if t = a then p else 0) + (if t = c then q else 0) + (if t = j then -1 else 0) := by
    intro t
    by_cases hta : t = a
    · subst hta
      simp [hac, hja.symm]
    · by_cases htc : t = c
      · subst htc
        simp [hta, hjc.symm]
      · simp [hta, htc]
  simp only [h, add_smul, Finset.sum_add_distrib, ite_smul, zero_smul, Finset.sum_ite_eq',
    ha, hc, hj, ↓reduceIte, neg_smul, one_smul, sub_eq_add_neg]

omit [Finite J] [P.IsReduced] in
/-- The coefficients of a root in the span of two simple roots have a common sign. -/
theorem sign_of_root_eq_pair (ha : a ∈ b.support) (hc : c ∈ b.support) (hac : a ≠ c) {α : J}
    {p q : ℤ} (h : P.root α = p • P.root a + q • P.root c) :
    (0 ≤ p ∧ 0 ≤ q) ∨ (p ≤ 0 ∧ q ≤ 0) := by
  let f : J → ℤ := fun j => if j = a then p else if j = c then q else 0
  have hf : ∑ j ∈ b.support, f j • P.root j ∈ Set.range P.root :=
    ⟨α, by rw [h, sum_pair_eq ha hc hac]⟩
  have hf₀ : Function.support f ⊆ b.support := by
    intro j hj
    by_cases hja : j = a
    · rw [hja]; exact ha
    · by_cases hjc : j = c
      · rw [hjc]; exact hc
      · exact absurd (by simp [f, hja, hjc]) hj
  rcases b.pos_or_neg_of_sum_smul_root_mem f hf hf₀ with hpos | hneg
  · left
    have h1 := hpos.le a
    have h2 := hpos.le c
    simp only [f, Pi.zero_apply, ↓reduceIte, hac.symm] at h1 h2
    exact ⟨h1, h2⟩
  · right
    have h1 := hneg.le a
    have h2 := hneg.le c
    simp only [f, Pi.zero_apply, ↓reduceIte, hac.symm] at h1 h2
    exact ⟨h1, h2⟩

omit [Finite J] [P.IsReduced] in
/-- The height of a root in the span of two simple roots. -/
theorem height_of_root_eq_pair (ha : a ∈ b.support) (hc : c ∈ b.support) (hac : a ≠ c)
    {α : J} {p q : ℤ} (h : P.root α = p • P.root a + q • P.root c) :
    b.height α = p + q := by
  rw [RootPairing.Base.height_eq_sum (f := fun j => if j = a then p else if j = c then q else 0)
    (by rw [h, sum_pair_eq ha hc hac])]
  have h' : ∀ j, (if j = a then p else if j = c then q else 0) =
      (if j = a then p else 0) + (if j = c then q else 0) := by
    intro j
    by_cases hja : j = a
    · subst hja
      simp [hac]
    · simp [hja]
  simp only [h', Finset.sum_add_distrib, Finset.sum_ite_eq', ha, hc, ↓reduceIte]

omit [P.IsReduced] in
/-- **Predecessors in a rank-two span.** A root `p • a + q • c` with `p, q ≥ 0` and
`p + q ≥ 2` has a root predecessor `(p - 1) • a + q • c` or `p • a + (q - 1) • c`. -/
theorem exists_pred_of_root_eq_pair (ha : a ∈ b.support) (hc : c ∈ b.support) (hac : a ≠ c)
    {α : J} {p q : ℤ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : 2 ≤ p + q)
    (h : P.root α = p • P.root a + q • P.root c) :
    ∃ α' : J, (1 ≤ p ∧ P.root α' = (p - 1) • P.root a + q • P.root c) ∨
      (1 ≤ q ∧ P.root α' = p • P.root a + (q - 1) • P.root c) := by
  have hht := height_of_root_eq_pair ha hc hac h
  have hpos : b.IsPos α := by
    rw [RootPairing.Base.isPos_iff, hht]
    omega
  obtain ⟨j, hj, hj'⟩ := hpos.exists_mem_support_pos_pairingIn
  have hj'' : 0 < P.pairingIn ℤ α j := (P.zero_lt_pairingIn_iff' ℤ (i := j) (j := α)).mp hj'
  have hαj : α ≠ j := by
    rintro rfl
    rw [RootPairing.Base.height_one_of_mem_support hj] at hht
    omega
  obtain ⟨α', hα'⟩ := P.root_sub_root_mem_of_pairingIn_pos hj'' hαj
  refine ⟨α', ?_⟩
  by_cases hja : j = a
  · subst hja
    left
    have h2 : P.root α' = (p - 1) • P.root j + q • P.root c := by
      rw [hα', h, sub_smul, one_smul]
      abel
    refine ⟨?_, h2⟩
    by_contra hp1
    have hp0 : p = 0 := by omega
    rcases sign_of_root_eq_pair hj hc hac h2 with h3 | h3 <;> omega
  · by_cases hjc : j = c
    · subst hjc
      right
      have h2 : P.root α' = p • P.root a + (q - 1) • P.root j := by
        rw [hα', h, sub_smul, one_smul]
        abel
      refine ⟨?_, h2⟩
      by_contra hq1
      have hq0 : q = 0 := by omega
      rcases sign_of_root_eq_pair ha hj hac h2 with h3 | h3 <;> omega
    · exfalso
      let f : J → ℤ := fun t => if t = a then p else if t = c then q else if t = j then -1 else 0
      have hf : ∑ t ∈ b.support, f t • P.root t ∈ Set.range P.root :=
        ⟨α', by rw [hα', h, sum_pair_sub_eq ha hc hac hj hja hjc]⟩
      have hf₀ : Function.support f ⊆ b.support := by
        intro t ht
        by_cases hta : t = a
        · rw [hta]; exact ha
        · by_cases htc : t = c
          · rw [htc]; exact hc
          · by_cases htj : t = j
            · rw [htj]; exact hj
            · exact absurd (by simp [f, hta, htc, htj]) ht
      have hfa : f a = p := by simp [f]
      have hfc : f c = q := by simp [f, hac.symm]
      have hfj : f j = -1 := by simp [f, hja, hjc]
      rcases b.pos_or_neg_of_sum_smul_root_mem f hf hf₀ with hpos' | hneg'
      · have := hpos'.le j
        rw [hfj] at this
        simp at this
      · have h1 := hneg'.le a
        have h2 := hneg'.le c
        rw [hfa] at h1
        rw [hfc] at h2
        simp only [Pi.zero_apply] at h1 h2
        omega

/-- **Roots of type `A₂`.** If `a`, `c` are distinct simple roots with
`⟨a, c^∨⟩ = ⟨c, a^∨⟩ = -1`, the roots `p • a + q • c` with `p, q ≥ 0` are `a`, `c` and
`a + c`. -/
theorem a2_coeffs_of_nonneg (ha : a ∈ b.support) (hc : c ∈ b.support) (hac : a ≠ c)
    (h1 : P.pairingIn ℤ a c = -1) (h2 : P.pairingIn ℤ c a = -1) :
    ∀ (n : ℕ) {α : J} {p q : ℤ}, p + q = n → 0 ≤ p → 0 ≤ q →
      P.root α = p • P.root a + q • P.root c →
      (p = 1 ∧ q = 0) ∨ (p = 0 ∧ q = 1) ∨ (p = 1 ∧ q = 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro α p q hn hp hq h
    have hli : LinearIndependent ℤ ![P.root a, P.root c] :=
      b.linearIndependent_pair_of_ne (i := ⟨a, ha⟩) (j := ⟨c, hc⟩)
        (fun h' => hac (congrArg Subtype.val h'))
    have hli' : LinearIndependent ℤ ![P.root c, P.root a] :=
      b.linearIndependent_pair_of_ne (i := ⟨c, hc⟩) (j := ⟨a, ha⟩)
        (fun h' => hac (congrArg Subtype.val h').symm)
    by_cases hn2 : n ≤ 2
    · interval_cases n
      · exfalso
        have hp0 : p = 0 := by omega
        have hq0 : q = 0 := by omega
        exact P.ne_zero α (by rw [h, hp0, hq0]; simp)
      · omega
      · rcases (show (p = 2 ∧ q = 0) ∨ (p = 0 ∧ q = 2) ∨ (p = 1 ∧ q = 1) by omega) with
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | hpq
        · exfalso
          exact P.nsmul_notMem_range_root (n := 2) (i := a)
            ⟨α, by rw [h]; simp [two_smul]⟩
        · exfalso
          exact P.nsmul_notMem_range_root (n := 2) (i := c)
            ⟨α, by rw [h]; simp [two_smul]⟩
        · exact Or.inr (Or.inr hpq)
    · obtain ⟨α', hα'⟩ := exists_pred_of_root_eq_pair ha hc hac hp hq (by omega) h
      rcases hα' with ⟨hp1, h'⟩ | ⟨hq1, h'⟩
      · have := ih (n - 1) (by omega) (p := p - 1) (q := q) (by omega) (by omega) hq h'
        have hpq : p = 2 ∧ q = 1 := by omega
        exfalso
        have hmem : P.root c + (2 : ℕ) • P.root a ∈ Set.range P.root :=
          ⟨α, by rw [h, hpq.1, hpq.2]; simp [two_smul]; abel⟩
        rw [RootPairing.root_add_nsmul_mem_range_iff_le_chainTopCoeff hli] at hmem
        have e : (P.chainTopCoeff a c : ℤ) = -P.pairingIn ℤ c a :=
          RootPairing.Base.chainTopCoeff_eq_of_ne (b := b) (i := ⟨a, ha⟩) (j := ⟨c, hc⟩)
            (fun h' => hac (congrArg Subtype.val h'))
        rw [h2] at e
        omega
      · have := ih (n - 1) (by omega) (p := p) (q := q - 1) (by omega) hp (by omega) h'
        have hpq : p = 1 ∧ q = 2 := by omega
        exfalso
        have hmem : P.root a + (2 : ℕ) • P.root c ∈ Set.range P.root :=
          ⟨α, by rw [h, hpq.1, hpq.2]; simp [two_smul]⟩
        rw [RootPairing.root_add_nsmul_mem_range_iff_le_chainTopCoeff hli'] at hmem
        have e : (P.chainTopCoeff c a : ℤ) = -P.pairingIn ℤ a c :=
          RootPairing.Base.chainTopCoeff_eq_of_ne (b := b) (i := ⟨c, hc⟩) (j := ⟨a, ha⟩)
            (fun h' => hac (congrArg Subtype.val h').symm)
        rw [h1] at e
        omega

/-- **Roots of type `A₂`, all signs.** If `a`, `c` are distinct simple roots with
`⟨a, c^∨⟩ = ⟨c, a^∨⟩ = -1`, the roots `p • a + q • c` with `p, q ∈ ℤ` are `±a`, `±c` and
`±(a + c)`. -/
theorem a2_coeffs (ha : a ∈ b.support) (hc : c ∈ b.support) (hac : a ≠ c)
    (h1 : P.pairingIn ℤ a c = -1) (h2 : P.pairingIn ℤ c a = -1) {α : J} {p q : ℤ}
    (h : P.root α = p • P.root a + q • P.root c) :
    (p = 1 ∧ q = 0) ∨ (p = 0 ∧ q = 1) ∨ (p = 1 ∧ q = 1) ∨
      (p = -1 ∧ q = 0) ∨ (p = 0 ∧ q = -1) ∨ (p = -1 ∧ q = -1) := by
  rcases sign_of_root_eq_pair ha hc hac h with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · rcases a2_coeffs_of_nonneg ha hc hac h1 h2 (p + q).toNat (by omega) hp hq h with h' | h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr (Or.inl h'))
  · have h' : P.root (P.reflectionPerm α α) = (-p) • P.root a + (-q) • P.root c := by
      rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self, h]
      simp only [neg_smul, neg_add]
    rcases a2_coeffs_of_nonneg ha hc hac h1 h2 (-p + -q).toNat (by omega) (by omega)
      (by omega) h' with h'' | h'' | h''
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by omega))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by omega)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by omega)))))

/-- **Roots of type `A₁ × A₁`.** If `a`, `c` are distinct simple roots with `⟨c, a^∨⟩ = 0`,
the roots `p • a + q • c` with `p, q ≥ 0` are `a` and `c`. -/
theorem a1a1_coeffs_of_nonneg (ha : a ∈ b.support) (hc : c ∈ b.support) (hac : a ≠ c)
    (h2 : P.pairingIn ℤ c a = 0) :
    ∀ (n : ℕ) {α : J} {p q : ℤ}, p + q = n → 0 ≤ p → 0 ≤ q →
      P.root α = p • P.root a + q • P.root c → (p = 1 ∧ q = 0) ∨ (p = 0 ∧ q = 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro α p q hn hp hq h
    have hli : LinearIndependent ℤ ![P.root a, P.root c] :=
      b.linearIndependent_pair_of_ne (i := ⟨a, ha⟩) (j := ⟨c, hc⟩)
        (fun h' => hac (congrArg Subtype.val h'))
    by_cases hn2 : n ≤ 2
    · interval_cases n
      · exfalso
        have hp0 : p = 0 := by omega
        have hq0 : q = 0 := by omega
        exact P.ne_zero α (by rw [h, hp0, hq0]; simp)
      · omega
      · exfalso
        rcases (show (p = 2 ∧ q = 0) ∨ (p = 0 ∧ q = 2) ∨ (p = 1 ∧ q = 1) by omega) with
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact P.nsmul_notMem_range_root (n := 2) (i := a)
            ⟨α, by rw [h]; simp [two_smul]⟩
        · exact P.nsmul_notMem_range_root (n := 2) (i := c)
            ⟨α, by rw [h]; simp [two_smul]⟩
        · have hmem : P.root c + (1 : ℕ) • P.root a ∈ Set.range P.root :=
            ⟨α, by rw [h]; simp; abel⟩
          rw [RootPairing.root_add_nsmul_mem_range_iff_le_chainTopCoeff hli] at hmem
          have e : (P.chainTopCoeff a c : ℤ) = -P.pairingIn ℤ c a :=
            RootPairing.Base.chainTopCoeff_eq_of_ne (b := b) (i := ⟨a, ha⟩) (j := ⟨c, hc⟩)
              (fun h' => hac (congrArg Subtype.val h'))
          rw [h2] at e
          omega
    · exfalso
      obtain ⟨α', hα'⟩ := exists_pred_of_root_eq_pair ha hc hac hp hq (by omega) h
      rcases hα' with ⟨hp1, h'⟩ | ⟨hq1, h'⟩
      · have := ih (n - 1) (by omega) (p := p - 1) (q := q) (by omega) (by omega) hq h'
        omega
      · have := ih (n - 1) (by omega) (p := p) (q := q - 1) (by omega) hp (by omega) h'
        omega

/-- **Roots of type `A₁ × A₁`, all signs.** -/
theorem a1a1_coeffs (ha : a ∈ b.support) (hc : c ∈ b.support) (hac : a ≠ c)
    (h2 : P.pairingIn ℤ c a = 0) {α : J} {p q : ℤ}
    (h : P.root α = p • P.root a + q • P.root c) :
    (p = 1 ∧ q = 0) ∨ (p = 0 ∧ q = 1) ∨ (p = -1 ∧ q = 0) ∨ (p = 0 ∧ q = -1) := by
  rcases sign_of_root_eq_pair ha hc hac h with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · rcases a1a1_coeffs_of_nonneg ha hc hac h2 (p + q).toNat (by omega) hp hq h with h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
  · have h' : P.root (P.reflectionPerm α α) = (-p) • P.root a + (-q) • P.root c := by
      rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self, h]
      simp only [neg_smul, neg_add]
    rcases a1a1_coeffs_of_nonneg ha hc hac h2 (-p + -q).toNat (by omega) (by omega)
      (by omega) h' with h'' | h''
    · exact Or.inr (Or.inr (Or.inl (by omega)))
    · exact Or.inr (Or.inr (Or.inr (by omega)))

end RankTwo

end Langlands.LinearAlgebra

namespace Langlands.GroupScheme

namespace LocalSplitCell

section TypeA2

variable {R : Type u} [CommRing R] {I : Type u} [Fintype I] [DecidableEq I] {J : Type u}
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G} {P : RootDatum J (I → ℤ) (I → ℤ)}
  {v : J → (Ga R ⟶ G)}

/-- **The `A₂` group computation**, in an abstract group. Let `X`, `Y`, `B`, `W` be additive
maps from a ring into a group. Suppose `(X x B y)⁻¹ (B y X x) = W (C x y)`,
`(Y x W y)⁻¹ (W y Y x) = B (D x y)`, `Y` commutes with `B`, `B` commutes with `W`, and
`W t = N B t N⁻¹` with `N = Y(-1) X(1) Y(-1)`. Then `B (1 - D C) = W (1 + C)`. -/
theorem a2_group_identity {Γ M : Type*} [CommRing Γ] [Group M] (X Y B W : Γ → M)
    (hX : ∀ s t, X (s + t) = X s * X t) (hY : ∀ s t, Y (s + t) = Y s * Y t)
    (hB : ∀ s t, B (s + t) = B s * B t) (hW : ∀ s t, W (s + t) = W s * W t) (C D : Γ)
    (hC : ∀ x y, (X x * B y)⁻¹ * (B y * X x) = W (C * x * y))
    (hD : ∀ x y, (Y x * W y)⁻¹ * (W y * Y x) = B (D * x * y))
    (hYB : ∀ x y, Y x * B y = B y * Y x) (hBW : ∀ x y, B x * W y = W y * B x)
    (hN : ∀ t, W t = (Y (-1) * X 1 * Y (-1)) * B t * (Y (-1) * X 1 * Y (-1))⁻¹) :
    B (1 - D * C) = W (1 + C) := by
  have hX0 : X 0 = 1 := by
    have h := hX 0 0
    rw [add_zero] at h
    exact (mul_eq_left.mp h.symm)
  have hY0 : Y 0 = 1 := by
    have h := hY 0 0
    rw [add_zero] at h
    exact (mul_eq_left.mp h.symm)
  have hW0 : W 0 = 1 := by
    have h := hW 0 0
    rw [add_zero] at h
    exact (mul_eq_left.mp h.symm)
  have hXinv : ∀ t, (X t)⁻¹ = X (-t) := fun t =>
    (eq_inv_of_mul_eq_one_left (by rw [← hX, neg_add_cancel, hX0])).symm
  have hYinv : ∀ t, (Y t)⁻¹ = Y (-t) := fun t =>
    (eq_inv_of_mul_eq_one_left (by rw [← hY, neg_add_cancel, hY0])).symm
  have hWinv : ∀ t, (W t)⁻¹ = W (-t) := fun t =>
    (eq_inv_of_mul_eq_one_left (by rw [← hW, neg_add_cancel, hW0])).symm
  -- (i) conjugating `B 1` by `X 1`
  have hi : ∀ z, X 1 * (B 1 * (X (-1) * z)) = B 1 * (W (-C) * z) := by
    intro z
    have h := hC (-1) 1
    rw [inv_mul_eq_iff_eq_mul, show C * -1 * 1 = -C by ring] at h
    have h' : X 1 * (B 1 * X (-1)) = B 1 * W (-C) := by
      rw [h, ← mul_assoc, ← mul_assoc, ← hX, add_neg_cancel, hX0, one_mul]
    rw [← mul_assoc (B 1), ← mul_assoc (X 1), h', mul_assoc]
  -- (ii) conjugating `W (-C)` by `Y (-1)`
  have hii : Y (-1) * (W (-C) * Y 1) = W (-C) * B (-(D * C)) := by
    have h := hD 1 (-C)
    rw [inv_mul_eq_iff_eq_mul, show D * 1 * -C = -(D * C) by ring] at h
    rw [h, ← mul_assoc, ← mul_assoc, ← hY, neg_add_cancel, hY0, one_mul]
  -- (iii) `Y (-1)` commutes with `B 1`
  have hiii : ∀ z, Y (-1) * (B 1 * z) = B 1 * (Y (-1) * z) := by
    intro z
    rw [← mul_assoc, hYB, mul_assoc]
  have hcancel : ∀ z, Y (-1) * (Y 1 * z) = z := by
    intro z
    rw [← mul_assoc, ← hY, neg_add_cancel, hY0, one_mul]
  have hW1 : W 1 = B (1 - D * C) * W (-C) := by
    rw [hN 1]
    simp only [mul_inv_rev, hYinv, hXinv, neg_neg, mul_assoc]
    rw [hiii, hcancel, hi, hiii, hii, ← hBW, ← mul_assoc, ← hB, sub_eq_add_neg]
  have h := congrArg (· * W C) hW1
  simp only [mul_assoc, ← hW, neg_add_cancel, hW0, mul_one] at h
  exact h.symm

omit [Fintype I] [DecidableEq I] in
/-- The root `s_a c = a + c` for two simple roots with `⟨c, a^∨⟩ = -1`. -/
theorem root_reflectionPerm_eq_add {a c : J} (h2 : P.pairingIn ℤ c a = -1) :
    P.root (P.reflectionPerm a c) = P.root a + P.root c := by
  have hp : P.pairing c a = -1 := by
    rw [← P.algebraMap_pairingIn ℤ, h2]
    simp
  rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_root, hp, neg_smul,
    one_smul, sub_neg_eq_add, add_comm]

/-- **The `A₂` commutator constants.** Let `a`, `c` be simple roots of some base with
`⟨a, c^∨⟩ = ⟨c, a^∨⟩ = -1`, and let `v` be root parametrizations of all roots such that
`n = v_{-a}(-1) v_a(1) v_{-a}(-1)` is a Weyl point acting by `s_a`. Put `w = Ad(n) ∘ v_c`, a
root parametrization of `a + c`. Then over every ring over `R`,
`(v_a(x) v_c(y))⁻¹ (v_c(y) v_a(x)) = w(-x y)` and
`(v_{-a}(x) w(y))⁻¹ (w(y) v_{-a}(x)) = v_c(-x y)`. -/
theorem a2_constants (hG : IsReductive G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (hP : IsFibrewiseRootDatumOf I G i P) (hv : ∀ α, IsRootParametrization i (P.root α) (v α))
    {b : P.Base} {a c : J} (ha : a ∈ b.support) (hc : c ∈ b.support) (hac : a ≠ c)
    (h1 : P.pairingIn ℤ a c = -1) (h2 : P.pairingIn ℤ c a = -1)
    (hn : IsWeylPoint i (weylPoint (v a) (v (P.reflectionPerm a a))) (P.reflection a)) :
    (∀ (B : Type u) [CommRing B] (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
      (x y : B),
      (rootPoint (v a) (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv x) *
          rootPoint (v c) (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv y))⁻¹ *
        (rootPoint (v c) (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv y) *
          rootPoint (v a) (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv x)) =
      rootPoint (v c ≫ (G.innerIso (weylPoint (v a) (v (P.reflectionPerm a a)))).hom)
        (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv (-(x * y)))) ∧
    (∀ (B : Type u) [CommRing B] (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
      (x y : B),
      (rootPoint (v (P.reflectionPerm a a)) (Over.mk s)
            ((Scheme.ΓSpecIso (CommRingCat.of B)).inv x) *
          rootPoint (v c ≫ (G.innerIso (weylPoint (v a) (v (P.reflectionPerm a a)))).hom)
            (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv y))⁻¹ *
        (rootPoint (v c ≫ (G.innerIso (weylPoint (v a) (v (P.reflectionPerm a a)))).hom)
            (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv y) *
          rootPoint (v (P.reflectionPerm a a)) (Over.mk s)
            ((Scheme.ΓSpecIso (CommRingCat.of B)).inv x)) =
      rootPoint (v c) (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv (-(x * y)))) := by
  classical
  have := hP.finite
  have : P.IsReduced := hP.isReduced
  set na := P.reflectionPerm a a with hna
  set n := weylPoint (v a) (v na) with hndef
  set w := v c ≫ (G.innerIso n).hom with hwdef
  set d := P.reflectionPerm a c with hddef
  have hd : P.root d = P.root a + P.root c := root_reflectionPerm_eq_add h2
  have hrna : P.root na = -P.root a := by
    rw [hna, RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self]
  have hli : LinearIndependent ℤ ![P.root a, P.root c] :=
    b.linearIndependent_pair_of_ne (i := ⟨a, ha⟩) (j := ⟨c, hc⟩)
      (fun h' => hac (congrArg Subtype.val h'))
  have hpair : ∀ s t : ℤ, s • P.root a + t • P.root c = 0 → s = 0 ∧ t = 0 :=
    fun s t h => LinearIndependent.pair_iff.mp hli s t h
  have hw : IsRootParametrization i (P.root d) w := by
    have h := (hv c).comp_innerIso hn
    rw [hddef, RootPairing.root_reflectionPerm]
    exact h
  -- distinctness of the indices
  have hda : d ≠ a := by
    intro h
    have h' := hd
    rw [h] at h'
    have := hpair 0 1 (by rw [zero_smul, one_smul, zero_add]; exact (add_eq_left.mp h'.symm))
    omega
  have hdc : d ≠ c := by
    intro h
    have h' := hd
    rw [h] at h'
    have := hpair 1 0 (by rw [zero_smul, one_smul, add_zero]; exact (add_eq_right.mp h'.symm))
    omega
  have hdna : d ≠ na := by
    intro h
    have h' := hd
    rw [h, hrna] at h'
    have := hpair 2 1 (by rw [two_smul, one_smul, add_assoc, ← h', add_neg_cancel])
    omega
  have hcna : c ≠ na := by
    intro h
    have h' : P.root c = -P.root a := by rw [h, hrna]
    exact b.root_ne_neg_of_ne hc ha (Ne.symm hac) h'
  have hana : a ≠ na := by
    intro h
    have h' : P.root a = -P.root a := by
      conv_lhs => rw [h]
      exact hrna
    have h3 : (2 : ℤ) • P.root a + (0 : ℤ) • P.root c = 0 := by
      rw [zero_smul, add_zero, two_smul]
      nth_rw 2 [h']
      exact add_neg_cancel _
    have := hpair 2 0 h3
    omega
  -- the family with `w` at `a + c`
  let v' : J → (Ga R ⟶ G) := Function.update v d w
  have hv'a : v' a = v a := Function.update_of_ne (Ne.symm hda) _ _
  have hv'c : v' c = v c := Function.update_of_ne (Ne.symm hdc) _ _
  have hv'na : v' na = v na := Function.update_of_ne (Ne.symm hdna) _ _
  have hv'd : v' d = w := Function.update_self _ _ _
  have hv' : ∀ α, IsRootParametrization i (P.root α) (v' α) := by
    intro α
    by_cases hα : α = d
    · subst hα
      rw [hv'd]
      exact hw
    · rw [show v' α = v α from Function.update_of_ne hα _ _]
      exact hv α
  -- root facts
  have hcoeff := fun {α : J} {p q : ℤ} (h : P.root α = p • P.root a + q • P.root c) =>
    Langlands.LinearAlgebra.a2_coeffs ha hc hac h1 h2 h
  have hac' : P.root a ≠ -P.root c := b.root_ne_neg_of_ne ha hc hac
  have hnad : P.root na ≠ -P.root d := by
    rw [hrna, hd, neg_add, ne_eq, left_eq_add, neg_eq_zero]
    exact P.ne_zero c
  have hnac : P.root na ≠ -P.root c := by
    rw [hrna, ne_eq, neg_inj]
    exact fun h => hac (P.root.injective h)
  have hcd : P.root c ≠ -P.root d := by
    intro h
    rw [hd] at h
    have h3 : (1 : ℤ) • P.root a + (2 : ℤ) • P.root c = 0 := by
      rw [one_smul, two_smul,
        show P.root a + (P.root c + P.root c) = P.root c + (P.root a + P.root c) by abel]
      nth_rw 1 [h]
      exact neg_add_cancel _
    have := hpair 1 2 h3
    omega
  have hcna' : P.root c = P.root na + P.root d := by
    rw [hrna, hd, neg_add_cancel_left]
  have hcone1 : ∀ (α : J) (dS dT : ℕ), 1 ≤ dS → 1 ≤ dT →
      (dS : ℤ) • P.root a + (dT : ℤ) • P.root c = P.root α → dS = 1 ∧ dT = 1 := by
    intro α dS dT hS hT h
    rcases hcoeff h.symm with h' | h' | h' | h' | h' | h' <;> omega
  have hcone2 : ∀ (α : J) (dS dT : ℕ), 1 ≤ dS → 1 ≤ dT →
      (dS : ℤ) • P.root na + (dT : ℤ) • P.root d = P.root α → dS = 1 ∧ dT = 1 := by
    intro α dS dT hS hT h
    have h' : P.root α = ((dT : ℤ) - dS) • P.root a + (dT : ℤ) • P.root c := by
      rw [← h, hrna, hd]
      module
    rcases hcoeff h' with h'' | h'' | h'' | h'' | h'' | h'' <;> omega
  have hcone3 : ∀ (α : J) (dS dT : ℕ), 1 ≤ dS → 1 ≤ dT →
      (dS : ℤ) • P.root na + (dT : ℤ) • P.root c ≠ P.root α := by
    intro α dS dT hS hT h
    have h' : P.root α = (-(dS : ℤ)) • P.root a + (dT : ℤ) • P.root c := by
      rw [← h, hrna]
      module
    rcases hcoeff h' with h'' | h'' | h'' | h'' | h'' | h'' <;> omega
  have hcone4 : ∀ (α : J) (dS dT : ℕ), 1 ≤ dS → 1 ≤ dT →
      (dS : ℤ) • P.root c + (dT : ℤ) • P.root d ≠ P.root α := by
    intro α dS dT hS hT h
    have h' : P.root α = (dT : ℤ) • P.root a + ((dS : ℤ) + dT) • P.root c := by
      rw [← h, hd]
      module
    rcases hcoeff h' with h'' | h'' | h'' | h'' | h'' | h'' <;> omega
  -- the commutator constants and commutations
  obtain ⟨C, hC⟩ := exists_rootPoint_comm_single hG hmax hP hv' hac' hd hcone1
  obtain ⟨D, hD⟩ := exists_rootPoint_comm_single hG hmax hP hv' hnad hcna' hcone2
  rw [hv'a, hv'c, hv'd] at hC
  rw [hv'na, hv'c, hv'd] at hD
  have hYB := fun {B : Type u} [CommRing B] (s : Spec (CommRingCat.of B) ⟶ _) x y =>
    rootPoint_commute_of_forall_ne hG hmax hP hv' hnac hcone3 (B := B) s x y
  have hBW := fun {B : Type u} [CommRing B] (s : Spec (CommRingCat.of B) ⟶ _) x y =>
    rootPoint_commute_of_forall_ne hG hmax hP hv' hcd hcone4 (B := B) s x y
  -- evaluation over `R` itself
  set s₀ : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of R) := 𝟙 _ with hs₀
  set e₀ := (Scheme.ΓSpecIso (CommRingCat.of R)).inv with he₀
  have hpre : ∀ r : R, (Spec.preimage s₀).hom r = r := by
    intro r
    rw [hs₀, Spec.preimage_id]
    rfl
  have hsurj : ∀ t : Γ((Over.mk s₀).left, ⊤), ∃ r : R, e₀ r = t :=
    fun t => ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom t, Iso.hom_inv_id_apply _ _⟩
  have hkey := a2_group_identity (fun t => rootPoint (v a) (Over.mk s₀) t)
    (fun t => rootPoint (v na) (Over.mk s₀) t) (fun t => rootPoint (v c) (Over.mk s₀) t)
    (fun t => rootPoint w (Over.mk s₀) t)
    (fun s t => rootPoint_add _ _ s t) (fun s t => rootPoint_add _ _ s t)
    (fun s t => rootPoint_add _ _ s t) (fun s t => rootPoint_add _ _ s t) (e₀ C) (e₀ D)
    (by
      intro x y
      obtain ⟨x₀, rfl⟩ := hsurj x
      obtain ⟨y₀, rfl⟩ := hsurj y
      have h := hC R s₀ x₀ y₀
      rw [hpre, map_mul, map_mul] at h
      exact h)
    (by
      intro x y
      obtain ⟨x₀, rfl⟩ := hsurj x
      obtain ⟨y₀, rfl⟩ := hsurj y
      have h := hD R s₀ x₀ y₀
      rw [hpre, map_mul, map_mul] at h
      exact h)
    (by
      intro x y
      have h := hYB s₀ x y
      rw [hv'na, hv'c] at h
      exact h)
    (by
      intro x y
      have h := hBW s₀ x y
      rw [hv'c, hv'd] at h
      exact h)
    (by
      intro t
      simp only [hwdef, rootPoint_comp, GroupScheme.comp_innerIso_hom, hndef,
        constantPoint_weylPoint])
  simp only at hkey
  -- uniqueness of coordinates in the big cell of `b`
  obtain ⟨m, n', neg, pos, hopen, -⟩ := exists_cell_of_base hG hmax hP hv' b
  have := hopen
  have hcpos : b.IsPos c := b.isPos_of_mem_support hc
  have hdpos : b.IsPos d := (b.isPos_of_mem_support ha).add hcpos hd
  set qc := pos.symm ⟨c, hcpos⟩ with hqc
  set qd := pos.symm ⟨d, hdpos⟩ with hqd
  have hqc' : ((pos qc : {α // b.IsPos α}) : J) = c := by simp [qc]
  have hqd' : ((pos qd : {α // b.IsPos α}) : J) = d := by simp [qd]
  have hq : qc ≠ qd := by
    intro h
    apply hdc
    rw [← hqd', ← hqc', h]
  have hcoord : ∀ r₁ r₂ : Γ((Over.mk s₀).left, ⊤),
      rootPoint (v c) (Over.mk s₀) r₁ = rootPoint w (Over.mk s₀) r₂ → r₁ = 0 ∧ r₂ = 0 := by
    intro r₁ r₂ h
    have h1 := orderedProduct_eq_rootPoint_of_eq_zero v' (fun k => (pos k : J)) (Over.mk s₀)
      (fun q => if q = qc then r₁ else 0) qc (fun l hl => by simp [hl])
    have h2 := orderedProduct_eq_rootPoint_of_eq_zero v' (fun k => (pos k : J)) (Over.mk s₀)
      (fun q => if q = qd then r₂ else 0) qd (fun l hl => by simp [hl])
    simp only [hqc', hqd', hv'c, hv'd, ↓reduceIte] at h1 h2
    have h3 := orderedProduct_pos_injective (i := i) (neg := fun k => (neg k : J))
      (Over.mk s₀) (h1.trans (h.trans h2.symm))
    have h4 := congrFun h3 qc
    have h5 := congrFun h3 qd
    simp only [hq, hq.symm, ↓reduceIte] at h4 h5
    exact ⟨h4, h5.symm⟩
  obtain ⟨hz1, hz2⟩ := hcoord _ _ hkey
  have hinj : ∀ r : R, e₀ r = 0 → r = 0 := by
    intro r hr
    have := congrArg (Scheme.ΓSpecIso (CommRingCat.of R)).hom hr
    rwa [he₀, Iso.inv_hom_id_apply, map_zero] at this
  have hC1 : 1 + C = 0 := hinj _ (by rw [map_add, map_one]; exact hz2)
  have hDC : 1 - D * C = 0 := hinj _ (by rw [map_sub, map_one, map_mul]; exact hz1)
  have hCv : C = -1 := by linear_combination hC1
  have hDv : D = -1 := by
    rw [hCv] at hDC
    linear_combination hDC
  refine ⟨fun B _ s x y => ?_, fun B _ s x y => ?_⟩
  · rw [hC B s x y, hCv, map_neg, map_one, neg_one_mul, neg_mul]
  · rw [hD B s x y, hDv, map_neg, map_one, neg_one_mul, neg_mul]

omit [DecidableEq I] in
/-- **Commuting root groups of type `A₁ × A₁`.** If `a`, `c` are simple roots of a base with
`⟨c, a^∨⟩ = 0`, then the root groups of `±a` commute with those of `±c` over every ring
over `R`. -/
theorem a1a1_commute (hG : IsReductive G)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (hP : IsFibrewiseRootDatumOf I G i P) (hv : ∀ α, IsRootParametrization i (P.root α) (v α))
    {b : P.Base} {a c : J} (ha : a ∈ b.support) (hc : c ∈ b.support) (hac : a ≠ c)
    (h2 : P.pairingIn ℤ c a = 0) {β ε : J}
    (hβ : P.root β = P.root a ∨ P.root β = -P.root a)
    (hε : P.root ε = P.root c ∨ P.root ε = -P.root c)
    {B : Type u} [CommRing B] (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
    (x y : Γ((Over.mk s).left, ⊤)) :
    rootPoint (v β) (Over.mk s) x * rootPoint (v ε) (Over.mk s) y =
      rootPoint (v ε) (Over.mk s) y * rootPoint (v β) (Over.mk s) x := by
  classical
  have := hP.finite
  have : P.IsReduced := hP.isReduced
  have hli : LinearIndependent ℤ ![P.root a, P.root c] :=
    b.linearIndependent_pair_of_ne (i := ⟨a, ha⟩) (j := ⟨c, hc⟩)
      (fun h' => hac (congrArg Subtype.val h'))
  obtain ⟨σ, hσ, hσβ⟩ : ∃ σ : ℤ, (σ = 1 ∨ σ = -1) ∧ P.root β = σ • P.root a := by
    rcases hβ with h | h
    · exact ⟨1, Or.inl rfl, by rw [h, one_smul]⟩
    · exact ⟨-1, Or.inr rfl, by rw [h, neg_one_smul]⟩
  obtain ⟨τ, hτ, hτε⟩ : ∃ τ : ℤ, (τ = 1 ∨ τ = -1) ∧ P.root ε = τ • P.root c := by
    rcases hε with h | h
    · exact ⟨1, Or.inl rfl, by rw [h, one_smul]⟩
    · exact ⟨-1, Or.inr rfl, by rw [h, neg_one_smul]⟩
  have hne : P.root β ≠ -P.root ε := by
    intro h
    rw [hσβ, hτε] at h
    have h' : σ • P.root a + τ • P.root c = 0 := by rw [h, neg_add_cancel]
    have := LinearIndependent.pair_iff.mp hli σ τ h'
    omega
  refine rootPoint_commute_of_forall_ne hG hmax hP hv hne ?_ s x y
  intro α dS dT hS hT h
  have h' : P.root α = ((dS : ℤ) * σ) • P.root a + ((dT : ℤ) * τ) • P.root c := by
    rw [← h, hσβ, hτε, mul_smul, mul_smul]
  rcases Langlands.LinearAlgebra.a1a1_coeffs ha hc hac h2 h' with h'' | h'' | h'' | h'' <;>
    rcases hσ with rfl | rfl <;> rcases hτ with rfl | rfl <;> omega

end TypeA2

end LocalSplitCell

open LocalSplitCell in
/-- **Commutators of type `A₂`.** For a reductive group scheme over a commutative ring with a
fibrewise maximal coordinate split torus `i`, a fibrewise root datum `P`, and root
parametrizations `v` of all roots, let `a`, `c` be simple roots of a base with
`⟨a, c^∨⟩ = ⟨c, a^∨⟩ = -1` such that `n = v_{-a}(-1) v_a(1) v_{-a}(-1)` is a Weyl point
acting by the reflection `s_a`. With `w = Ad(n) ∘ v_c`, over every ring over `R`:
`(v_a(x) v_c(y))⁻¹ (v_c(y) v_a(x)) = w(-x y)` and
`(v_{-a}(x) w(y))⁻¹ (w(y) v_{-a}(x)) = v_c(-x y)`. -/
def LocalSplitTypeA2CommutatorStatement : Prop :=
  ∀ (R : Type u) [CommRing R] (I : Type u) [Fintype I] [DecidableEq I] (J : Type u)
    (G : GroupScheme (Spec (CommRingCat.of R))) [IsAffineHom G.X.hom], IsReductive G →
    ∀ (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G),
    IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i →
    ∀ (P : RootDatum J (I → ℤ) (I → ℤ)), IsFibrewiseRootDatumOf I G i P →
    ∀ (v : J → (Ga R ⟶ G)), (∀ α, IsRootParametrization i (P.root α) (v α)) →
    ∀ (b : P.Base) (a c : J), a ∈ b.support → c ∈ b.support → a ≠ c →
    P.pairingIn ℤ a c = -1 → P.pairingIn ℤ c a = -1 →
    IsWeylPoint i (weylPoint (v a) (v (P.reflectionPerm a a))) (P.reflection a) →
    (∀ (B : Type u) [CommRing B] (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
      (x y : B),
      (rootPoint (v a) (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv x) *
          rootPoint (v c) (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv y))⁻¹ *
        (rootPoint (v c) (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv y) *
          rootPoint (v a) (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv x)) =
      rootPoint (v c ≫ (G.innerIso (weylPoint (v a) (v (P.reflectionPerm a a)))).hom)
        (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv (-(x * y)))) ∧
    (∀ (B : Type u) [CommRing B] (s : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of R))
      (x y : B),
      (rootPoint (v (P.reflectionPerm a a)) (Over.mk s)
            ((Scheme.ΓSpecIso (CommRingCat.of B)).inv x) *
          rootPoint (v c ≫ (G.innerIso (weylPoint (v a) (v (P.reflectionPerm a a)))).hom)
            (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv y))⁻¹ *
        (rootPoint (v c ≫ (G.innerIso (weylPoint (v a) (v (P.reflectionPerm a a)))).hom)
            (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv y) *
          rootPoint (v (P.reflectionPerm a a)) (Over.mk s)
            ((Scheme.ΓSpecIso (CommRingCat.of B)).inv x)) =
      rootPoint (v c) (Over.mk s) ((Scheme.ΓSpecIso (CommRingCat.of B)).inv (-(x * y))))

open LocalSplitCell in
/-- The `A₂` commutator statement holds at full universe. -/
theorem localSplitTypeA2Commutator : LocalSplitTypeA2CommutatorStatement.{u} := by
  intro R _ I _ _ J G _ hG i hmax P hP v hv b a c ha hc hac h1 h2 hn
  exact a2_constants hG hmax hP hv ha hc hac h1 h2 hn

end Langlands.GroupScheme
