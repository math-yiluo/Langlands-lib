import Langlands.GroupScheme.Reductive.LocalSplitWeylChains

/-! # Common Weyl conjugation from source geometry and target identities -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.LocalSplitCell

variable {R : Type u} [CommRing R] {I J : Type u}
  {P : RootDatum J (I → ℤ) (I → ℤ)} {b : P.Base}
  {W : ∀ α, SimpleWord P b α}

/-- Target map identities sufficient for the source-root height induction.
No target torus or target parametrization occurs in these fields. -/
structure TargetWeylRelations (P : RootDatum J (I → ℤ) (I → ℤ))
    (b : P.Base) (W : ∀ α, SimpleWord P b α)
    {H : GroupScheme (Spec (CommRingCat.of R))} (v : J → (Ga R ⟶ H)) : Prop where
  braids : WordBraids P b v
  square : ∀ c ∈ b.support, ∀ a,
    wordConj P v [c, c] (weylFamily P W v a) =
      scaleHom (signUnit R (P.pairingIn ℤ a c) : R) ≫ weylFamily P W v a
  fixed : ∀ c ∈ b.support, ∀ a,
    P.root a ≠ -P.root c →
    (∀ (d : J) (s t : ℕ), 1 ≤ s → 1 ≤ t →
      (s : ℤ) • P.root a + (t : ℤ) • P.root c ≠ P.root d) →
    P.root a ≠ -P.root (P.reflectionPerm c c) →
    (∀ (d : J) (s t : ℕ), 1 ≤ s → 1 ≤ t →
      (s : ℤ) • P.root a + (t : ℤ) • P.root (P.reflectionPerm c c) ≠ P.root d) →
    wordConj P v [c] (weylFamily P W v a) = weylFamily P W v a
  a2 : ∀ c ∈ b.support, ∀ j ∈ b.support, c ≠ j →
    P.pairingIn ℤ c j = -1 → P.pairingIn ℤ j c = -1 →
      wordConj P v [c] (v j) =
        scaleHom ((-1 : Rˣ) : R) ≫ wordConj P v [j] (v c)
  b2 : ∀ a ∈ b.support, ∀ c ∈ b.support, a ≠ c →
    P.pairingIn ℤ a c = -1 → P.pairingIn ℤ c a = -2 →
      wordConj P v [a] (wordConj P v [c] (v a)) =
        scaleHom ((-1 : Rˣ) : R) ≫ wordConj P v [c] (v a)
  simple : ∀ c ∈ b.support,
    wordConj P v [c] (weylFamily P W v c) =
      weylFamily P W v (P.reflectionPerm c c)
  negative : ∀ c ∈ b.support, ∀ a, b.IsPos a → b.IsPos (P.reflectionPerm c a) →
    ∀ κ : Rˣ,
    wordConj P v [c] (weylFamily P W v a) =
      scaleHom (κ : R) ≫ weylFamily P W v (P.reflectionPerm c a) →
    wordConj P v [c] (weylFamily P W v (P.reflectionPerm a a)) =
      scaleHom ((κ⁻¹ : Rˣ) : R) ≫
        weylFamily P W v (P.reflectionPerm c (P.reflectionPerm a a))

/-- The simple-root bookkeeping depends only on the descending words. -/
theorem weylFamily_simple_of_words {H : GroupScheme (Spec (CommRingCat.of R))}
    {u : J → (Ga R ⟶ H)} (hW : IsDescendingWords P b W) {a : J}
    (ha : a ∈ b.support) : weylFamily P W u a = u a := by
  unfold weylFamily
  rw [(hW.1 a ha).1, (hW.1 a ha).2]
  rfl

namespace TargetWeylRelations

variable {H : GroupScheme (Spec (CommRingCat.of R))}
  {v : J → (Ga R ⟶ H)}

/-- Source coefficient exclusions supply the two no-cone inputs of the fixed law. -/
theorem wordConj_fix_of_coeffs (hT : TargetWeylRelations P b W v)
    {c j : J} (hc : c ∈ b.support) (hj : j ∈ b.support) (hcj : c ≠ j) {β : J}
    {m n : ℤ} (hβ : P.root β = m • P.root c + n • P.root j) {Φ : ℤ → ℤ → Prop}
    (hΦ : ∀ (α : J) (m n : ℤ), P.root α = m • P.root c + n • P.root j → Φ m n)
    (hopp₁ : m + 1 ≠ 0 ∨ n + 0 ≠ 0)
    (hno₁ : ∀ dS dT : ℤ, 1 ≤ dS → 1 ≤ dT →
      Φ (dS * m + dT * 1) (dS * n + dT * 0) → False)
    (hopp₂ : m + -1 ≠ 0 ∨ n + 0 ≠ 0)
    (hno₂ : ∀ dS dT : ℤ, 1 ≤ dS → 1 ≤ dT →
      Φ (dS * m + dT * -1) (dS * n + dT * 0) → False) :
    wordConj P v [c] (weylFamily P W v β) = weylFamily P W v β := by
  have hli : LinearIndependent ℤ ![P.root c, P.root j] :=
    b.linearIndependent_pair_of_ne (i := ⟨c, hc⟩) (j := ⟨j, hj⟩)
      (fun h' => hcj (congrArg Subtype.val h'))
  have hc' : P.root c = (1 : ℤ) • P.root c + (0 : ℤ) • P.root j := by module
  have hnc' : P.root (P.reflectionPerm c c) =
      (-1 : ℤ) • P.root c + (0 : ℤ) • P.root j := by
    rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self]
    module
  have k₁ := noOpp_cone_of_coeffs hli hβ hc' hΦ hopp₁ hno₁
  have k₂ := noOpp_cone_of_coeffs hli hβ hnc' hΦ hopp₂ hno₂
  exact hT.fixed c hc β k₁.1 k₁.2 k₂.1 k₂.2

end TargetWeylRelations

namespace TargetWeylProofs

open Langlands.LinearAlgebra (a1a1_coeffs a2_coeffs b2_coeffs g2_coeffs)

variable [IsLocalRing R] [Fintype I] [DecidableEq I]
  {G H : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {u : J → (Ga R ⟶ G)} {u' : J → (Ga R ⟶ H)}

/-- **A root in the span of its descending letter and `c`.** -/
theorem univRel_top_span (hdG : IsNormalSimpleData i P b W u)
    (hT : TargetWeylRelations P b W u') {c j α : J} (hc : c ∈ b.support)
    (hj : j ∈ b.support) (hcj : c ≠ j) (hα : b.IsPos α) (hαs : α ∉ b.support)
    (hx : 0 ≤ P.pairing α c) (hy : 0 < P.pairing α j) {x y : ℤ}
    (hxy : P.root α = x • P.root c + y • P.root j)
    (hdefG : wordConj P u [j] (weylFamily P W u (P.reflectionPerm j α)) = weylFamily P W u α)
    (hdefH : wordConj P u' [j] (weylFamily P W u' (P.reflectionPerm j α)) =
      weylFamily P W u' α) :
    UnivRel P u u' [c] (weylFamily P W u (P.reflectionPerm c α)) (weylFamily P W u α)
      (weylFamily P W u' (P.reflectionPerm c α)) (weylFamily P W u' α) := by
  classical
  have := hdG.rootDatum.finite
  have : P.IsReduced := hdG.rootDatum.isReduced
  have hht : b.height α = x + y := by
    rw [height_of_root_eq_combo b hxy, RootPairing.Base.height_one_of_mem_support hc,
      RootPairing.Base.height_one_of_mem_support hj]
    ring
  have hpos : 0 < x + y := hht ▸ hα
  have hns1 : ¬ (x = 1 ∧ y = 0) := by
    rintro ⟨rfl, rfl⟩
    apply hαs
    have : α = c := P.root.injective (by rw [hxy]; module)
    rw [this]
    exact hc
  have hns2 : ¬ (x = 0 ∧ y = 1) := by
    rintro ⟨rfl, rfl⟩
    apply hαs
    have : α = j := P.root.injective (by rw [hxy]; module)
    rw [this]
    exact hj
  have hpc : P.pairing α c = x * 2 + y * P.pairing j c := by
    rw [pairing_combo (a := c) (c := j) hxy c, RootPairing.pairing_same]
  have hpj : P.pairing α j = x * P.pairing c j + y * 2 := by
    rw [pairing_combo (a := c) (c := j) hxy j, RootPairing.pairing_same]
  have hxy' : P.root α = y • P.root j + x • P.root c := by rw [hxy, add_comm]
  have hfix : ∀ {m n : ℤ}, P.root α = m • P.root c + n • P.root j →
      P.pairingIn ℤ α c = 0 → ∀ {Φ : ℤ → ℤ → Prop},
      (∀ (g : J) (m n : ℤ), P.root g = m • P.root c + n • P.root j → Φ m n) →
      (m + 1 ≠ 0 ∨ n + 0 ≠ 0) →
      (∀ dS dT : ℤ, 1 ≤ dS → 1 ≤ dT → Φ (dS * m + dT * 1) (dS * n + dT * 0) → False) →
      (m + -1 ≠ 0 ∨ n + 0 ≠ 0) →
      (∀ dS dT : ℤ, 1 ≤ dS → 1 ≤ dT → Φ (dS * m + dT * -1) (dS * n + dT * 0) → False) →
      UnivRel P u u' [c] (weylFamily P W u (P.reflectionPerm c α)) (weylFamily P W u α)
        (weylFamily P W u' (P.reflectionPerm c α)) (weylFamily P W u' α) := by
    intro m n hβ h0 Φ hΦ ho₁ hn₁ ho₂ hn₂
    have hsc : P.reflectionPerm c α = α := P.root.injective (by
      rw [root_reflectionPerm_eq, ← pairingIn_eq_pairing, h0, neg_zero, zero_smul, add_zero])
    rw [hsc]
    exact UnivRel.of_eq
      (hdG.wordConj_fix_of_coeffs hc hj hcj (hdG.isRootParametrization α) h0 hβ hΦ ho₁ hn₁ ho₂
        hn₂)
      (hT.wordConj_fix_of_coeffs hc hj hcj hβ hΦ ho₁ hn₁ ho₂
        hn₂)
  rcases simple_pair_cases hc hj hcj with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩
  · -- type `A₁ × A₁`: no non-simple positive root in the span
    rw [pairing_eq_of_pairingIn h1] at hpj
    rw [pairing_eq_of_pairingIn h2] at hpc
    rcases a1a1_coeffs hc hj hcj h2 hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      omega
  · -- type `A₂`: `α = c + j`
    rw [pairing_eq_of_pairingIn h1] at hpj
    rw [pairing_eq_of_pairingIn h2] at hpc
    rcases a2_coeffs hc hj hcj h1 h2 hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · omega
    · omega
    · have hsc : P.reflectionPerm c α = j := P.root.injective (by
        rw [root_reflectionPerm_eq, hxy, hpc]
        module)
      have hsj : P.reflectionPerm j α = c := P.root.injective (by
        rw [root_reflectionPerm_eq, hxy, hpj]
        module)
      rw [hsc]
      rw [hsj] at hdefG hdefH
      refine ⟨-1, ?_, ?_⟩
      · rw [hdG.weylFamily_simple hj, hdG.wordConj_a2 hc hj hcj h1 h2,
          ← hdG.weylFamily_simple hc, hdefG]
      · rw [weylFamily_simple_of_words (u := u') hdG.words hj, hT.a2 c hc j hj hcj h1 h2,
          ← weylFamily_simple_of_words (u := u') hdG.words hc, hdefH]
    all_goals omega
  · -- type `B₂`, `c` short: `α = c + j`
    rw [pairing_eq_of_pairingIn h1] at hpj
    rw [pairing_eq_of_pairingIn h2] at hpc
    rcases b2_coeffs hc hj hcj h1 h2 hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · omega
    · omega
    · have hsc : P.reflectionPerm c α = α := P.root.injective (by
        rw [root_reflectionPerm_eq, hpc]
        module)
      have hsj : P.reflectionPerm j α = c := P.root.injective (by
        rw [root_reflectionPerm_eq, hxy, hpj]
        module)
      rw [hsc]
      rw [hsj] at hdefG hdefH
      refine ⟨-1, ?_, ?_⟩
      · rw [← hdefG, hdG.weylFamily_simple hc, hdG.wordConj_b2 hc hj hcj h1 h2]
      · rw [← hdefH, weylFamily_simple_of_words (u := u') hdG.words hc, hT.b2 c hc j hj hcj h1 h2]
    all_goals omega
  · -- type `B₂`, `c` long: `α = c + 2j`
    rw [pairing_eq_of_pairingIn h1] at hpj
    rw [pairing_eq_of_pairingIn h2] at hpc
    rcases b2_coeffs hj hc hcj.symm h2 h1 hxy' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · omega
    · omega
    · omega
    · refine hfix (m := 1) (n := 2) (by rw [hxy]) (by rw [pairingIn_eq_pairing, hpc]; norm_num)
        (Φ := fun m n => (n = 1 ∧ m = 0) ∨ (n = 0 ∧ m = 1) ∨ (n = 1 ∧ m = 1) ∨ (n = 2 ∧ m = 1) ∨
          (n = -1 ∧ m = 0) ∨ (n = 0 ∧ m = -1) ∨ (n = -1 ∧ m = -1) ∨ (n = -2 ∧ m = -1))
        (fun g m n h => b2_coeffs hj hc hcj.symm h2 h1 (by rw [h, add_comm]))
        (by omega) (fun dS dT h₁ h₂ h => by omega) (by omega) (fun dS dT h₁ h₂ h => by omega)
    all_goals omega
  · -- type `G₂`, `c` short: `α = 3c + 2j`
    rw [pairing_eq_of_pairingIn h1] at hpj
    rw [pairing_eq_of_pairingIn h2] at hpc
    rcases g2_coeffs hc hj hcj h1 h2 hxy with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · omega
    · omega
    · omega
    · omega
    · omega
    · refine hfix (m := 3) (n := 2) hxy (by rw [pairingIn_eq_pairing, hpc]; norm_num)
        (Φ := fun m n => ((m = 1 ∧ n = 0) ∨ (m = 0 ∧ n = 1) ∨ (m = 1 ∧ n = 1) ∨ (m = 2 ∧ n = 1) ∨
          (m = 3 ∧ n = 1) ∨ (m = 3 ∧ n = 2)) ∨ ((m = -1 ∧ n = 0) ∨ (m = 0 ∧ n = -1) ∨
          (m = -1 ∧ n = -1) ∨ (m = -2 ∧ n = -1) ∨ (m = -3 ∧ n = -1) ∨ (m = -3 ∧ n = -2)))
        (fun g m n h => g2_coeffs hc hj hcj h1 h2 h)
        (by omega) (fun dS dT h₁ h₂ h => by omega) (by omega) (fun dS dT h₁ h₂ h => by omega)
    all_goals omega
  · -- type `G₂`, `c` long: `α = c + 2j`
    rw [pairing_eq_of_pairingIn h1] at hpj
    rw [pairing_eq_of_pairingIn h2] at hpc
    rcases g2_coeffs hj hc hcj.symm h2 h1 hxy' with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · omega
    · omega
    · omega
    · refine hfix (m := 1) (n := 2) (by rw [hxy]) (by rw [pairingIn_eq_pairing, hpc]; norm_num)
        (Φ := fun m n => ((n = 1 ∧ m = 0) ∨ (n = 0 ∧ m = 1) ∨ (n = 1 ∧ m = 1) ∨ (n = 2 ∧ m = 1) ∨
          (n = 3 ∧ m = 1) ∨ (n = 3 ∧ m = 2)) ∨ ((n = -1 ∧ m = 0) ∨ (n = 0 ∧ m = -1) ∨
          (n = -1 ∧ m = -1) ∨ (n = -2 ∧ m = -1) ∨ (n = -3 ∧ m = -1) ∨ (n = -3 ∧ m = -2)))
        (fun g m n h => g2_coeffs hj hc hcj.symm h2 h1 (by rw [h, add_comm]))
        (by omega) (fun dS dT h₁ h₂ h => by omega) (by omega) (fun dS dT h₁ h₂ h => by omega)
    all_goals omega

/-- **The inductive step for positive roots.** Let `α` and `s_c α` be positive with
`⟨α, c^∨⟩ ≥ 0`. If every step between positive roots of smaller height has a common
rescaling, so does the step `s_c α ↦ α`. -/
theorem univRel_top (hdG : IsNormalSimpleData i P b W u) (hT : TargetWeylRelations P b W u')
    (hbG : WordBraids P b u) {c : J} (hc : c ∈ b.support) {α : J}
    (hα : b.IsPos α) (hcα : b.IsPos (P.reflectionPerm c α)) (hx : 0 ≤ P.pairing α c)
    (hIH : ∀ k ∈ b.support, ∀ g : J, b.IsPos g → b.IsPos (P.reflectionPerm k g) →
      b.height g < b.height α → b.height (P.reflectionPerm k g) < b.height α →
      UnivRel P u u' [k] (weylFamily P W u (P.reflectionPerm k g)) (weylFamily P W u g)
        (weylFamily P W u' (P.reflectionPerm k g)) (weylFamily P W u' g)) :
    UnivRel P u u' [c] (weylFamily P W u (P.reflectionPerm c α)) (weylFamily P W u α)
      (weylFamily P W u' (P.reflectionPerm c α)) (weylFamily P W u' α) := by
  classical
  have := hdG.rootDatum.finite
  have : P.IsReduced := hdG.rootDatum.isReduced
  by_cases hαs : α ∈ b.support
  · by_cases hαc : α = c
    · subst hαc
      exact absurd hα ((RootPairing.Base.IsPos.neg_iff_not (b := b) α).mp hcα)
    · have hle : P.pairingIn ℤ α c ≤ 0 := b.pairingIn_le_zero_of_ne hαc hαs hc
      have h0 : P.pairingIn ℤ α c = 0 := by
        rw [pairingIn_eq_pairing] at hle ⊢
        omega
      have hsc : P.reflectionPerm c α = α := P.root.injective (by
        rw [root_reflectionPerm_eq, ← pairingIn_eq_pairing, h0, neg_zero, zero_smul, add_zero])
      rw [hsc]
      have hcα' : c ≠ α := Ne.symm hαc
      have hβ : P.root α = (0 : ℤ) • P.root c + (1 : ℤ) • P.root α := by module
      exact UnivRel.of_eq
        (hdG.wordConj_fix_of_coeffs hc hαs hcα' (hdG.isRootParametrization α) h0 hβ
          (fun g m n h => Langlands.LinearAlgebra.a1a1_coeffs hc hαs hcα' h0 h) (by omega)
          (fun dS dT h₁ h₂ h => by omega) (by omega) (fun dS dT h₁ h₂ h => by omega))
        (hT.wordConj_fix_of_coeffs hc hαs hcα' hβ
          (fun g m n h => Langlands.LinearAlgebra.a1a1_coeffs hc hαs hcα' h0 h) (by omega)
          (fun dS dT h₁ h₂ h => by omega) (by omega) (fun dS dT h₁ h₂ h => by omega))
  · obtain ⟨j, hj, hpj, hsimple, hword⟩ := hdG.words.2.1 α hα hαs
    have hdefG := weylFamily_descend (u := u) hsimple hword
    have hdefH := weylFamily_descend (u := u') hsimple hword
    by_cases hjc : j = c
    · subst hjc
      exact UnivRel.of_eq hdefG hdefH
    · have hcj : c ≠ j := Ne.symm hjc
      by_cases hspan : ∃ x y : ℤ, P.root α = x • P.root c + y • P.root j
      · obtain ⟨x, y, hxy⟩ := hspan
        exact univRel_top_span hdG hT hc hj hcj hα hαs hx hpj hxy hdefG hdefH
      · push Not at hspan
        exact univRel_twoPath hc hj hα hspan hx hpj (one_le_braidLength _)
          (twoChains_of_cases (simple_pair_cases hc hj hcj)) (hbG c hc j hj hcj)
          (hT.braids c hc j hj hcj) _ _
          (fun t g h₁ h₂ h₃ h₄ => hIH _ (by cases t <;> assumption) g h₁ h₂ h₃ h₄)
          (UnivRel.of_eq hdefG hdefH)

/-- **Common rescalings between positive roots.** For every simple root `c` and positive
roots `α`, `s_c α`, the step `s_c α ↦ α` has a common rescaling. -/
theorem univRel_positive (hdG : IsNormalSimpleData i P b W u)
    (hT : TargetWeylRelations P b W u') (hbG : WordBraids P b u) :
    ∀ (n : ℕ) {c : J}, c ∈ b.support → ∀ {α : J}, b.IsPos α → b.IsPos (P.reflectionPerm c α) →
      b.height α ≤ n → b.height (P.reflectionPerm c α) ≤ n →
      UnivRel P u u' [c] (weylFamily P W u (P.reflectionPerm c α)) (weylFamily P W u α)
        (weylFamily P W u' (P.reflectionPerm c α)) (weylFamily P W u' α) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro c hc α hα hcα h₁ h₂
    have hIH : ∀ g₀ : J, b.height g₀ ≤ n → 0 < b.height g₀ → ∀ k ∈ b.support, ∀ g : J,
        b.IsPos g → b.IsPos (P.reflectionPerm k g) → b.height g < b.height g₀ →
        b.height (P.reflectionPerm k g) < b.height g₀ →
        UnivRel P u u' [k] (weylFamily P W u (P.reflectionPerm k g)) (weylFamily P W u g)
          (weylFamily P W u' (P.reflectionPerm k g)) (weylFamily P W u' g) := by
      intro g₀ hg₀ hg₀' k hk g hg hkg e₁ e₂
      exact ih (b.height g₀ - 1).toNat (by omega) hk hg hkg (by omega) (by omega)
    by_cases hx : 0 ≤ P.pairing α c
    · exact univRel_top hdG hT hbG hc hα hcα hx (hIH α h₁ hα)
    · have hββ : P.reflectionPerm c (P.reflectionPerm c α) = α :=
        RootPairing.reflectionPerm_self _ _ _
      have hxβ : 0 ≤ P.pairing (P.reflectionPerm c α) c := by
        rw [pairing_of_root_eq (root_reflectionPerm_eq c α), RootPairing.pairing_same]
        omega
      have key := univRel_top hdG hT hbG hc hcα (by rw [hββ]; exact hα) hxβ
        (hIH _ h₂ hcα)
      rw [hββ] at key
      exact key.inv ⟨signUnit R (P.pairingIn ℤ α c),
        wordConj_sq hdG.rootDatum (hdG.rankOne c hc) (hdG.isRootParametrization α),
        hT.square c hc α⟩


/-- Common Weyl conjugation units from source partner geometry and target identities. -/
theorem weylConjugationRelations_of_targetLaws (hdG : IsNormalSimpleData i P b W u)
    (hT : TargetWeylRelations P b W u') (hPUG : PartnerUnique P G i)
    (hSCG : PartnerRescales P G i) : WeylConjugationRelations P b W u u' := by
  classical
  have := hdG.rootDatum.finite
  have : P.IsReduced := hdG.rootDatum.isReduced
  have hbG := wordBraids_of_partnerUnique hdG hPUG
  intro c hc d
  have hpos : ∀ {α : J}, b.IsPos α → α ≠ c →
      UnivRel P u u' [c] (weylFamily P W u α) (weylFamily P W u (P.reflectionPerm c α))
        (weylFamily P W u' α) (weylFamily P W u' (P.reflectionPerm c α)) := by
    intro α hα hαc
    have hcα : b.IsPos (P.reflectionPerm c α) := hα.reflectionPerm hc hαc
    have key := univRel_positive hdG hT hbG
      (max (b.height α).toNat (b.height (P.reflectionPerm c α)).toNat) hc
      (α := P.reflectionPerm c α)
      hcα (by rw [RootPairing.reflectionPerm_self]; exact hα) (by omega)
      (by rw [RootPairing.reflectionPerm_self]; omega)
    rwa [RootPairing.reflectionPerm_self] at key
  by_cases hdpos : b.IsPos d
  · by_cases hdc : d = c
    · subst hdc
      refine ⟨1, ?_, ?_⟩
      · rw [Units.val_one, scaleHom_one, Category.id_comp]
        exact hdG.wordConj_weylFamily_simple hc
      · rw [Units.val_one, scaleHom_one, Category.id_comp]
        exact hT.simple _ hc
    · exact hpos hdpos hdc
  · obtain ⟨α, hα, rfl⟩ : ∃ α, b.IsPos α ∧ d = P.reflectionPerm α α :=
      ⟨P.reflectionPerm d d, (RootPairing.Base.IsPos.neg_iff_not (b := b) d).mpr hdpos,
        (reflectionPerm_neg_self d).symm⟩
    by_cases hαc : α = c
    · subst hαc
      refine ⟨1, ?_, ?_⟩
      · change wordConj P u [α] (weylFamily P W u (P.reflectionPerm α α)) = _
        rw [← hdG.wordConj_weylFamily_simple hc, RootPairing.reflectionPerm_self, Units.val_one,
          scaleHom_one, Category.id_comp]
        change wordConj P u [α, α] (weylFamily P W u α) = _
        rw [wordConj_sq hdG.rootDatum (hdG.rankOne α hc) (hdG.isRootParametrization α),
          RootPairing.pairingIn_same, signUnit_even ⟨1, by norm_num⟩, Units.val_one, scaleHom_one,
          Category.id_comp]
      · change wordConj P u' [α] (weylFamily P W u' (P.reflectionPerm α α)) = _
        rw [← hT.simple α hc, RootPairing.reflectionPerm_self, Units.val_one,
          scaleHom_one, Category.id_comp]
        change wordConj P u' [α, α] (weylFamily P W u' α) = _
        rw [hT.square α hc α,
          RootPairing.pairingIn_same, signUnit_even ⟨1, by norm_num⟩, Units.val_one, scaleHom_one,
          Category.id_comp]
    · obtain ⟨κ, e₁, e₂⟩ := hpos hα hαc
      have hcα : b.IsPos (P.reflectionPerm c α) := hα.reflectionPerm hc hαc
      exact ⟨κ⁻¹, hdG.conj_neg hPUG hSCG hc hα hcα e₁, hT.negative c hc α hα hcα κ e₂⟩


end TargetWeylProofs

end Langlands.GroupScheme.LocalSplitCell

namespace Langlands.GroupScheme

open LocalSplitCell

/-- The Weyl-conjugation induction needs source geometry and explicit target identities. -/
def LocalSplitTargetWeylConjugationStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R]
    (I J : Type u) [Fintype I] [DecidableEq I]
    (P : RootDatum J (I → ℤ) (I → ℤ))
    (G H : GroupScheme (Spec (CommRingCat.of R))) [IsAffineHom G.X.hom]
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (b : P.Base) (W : ∀ α, SimpleWord P b α)
    (u : J → (Ga R ⟶ G)) (v : J → (Ga R ⟶ H)),
    IsNormalSimpleData i P b W u → PartnerUnique P G i → PartnerRescales P G i →
    TargetWeylRelations P b W v → WeylConjugationRelations P b W u v

/-- The explicit target identities suffice in every universe. -/
theorem localSplitTargetWeylConjugation :
    LocalSplitTargetWeylConjugationStatement.{u} := by
  intro R _ _ I J _ _ P G H _ i b W u v hd hPU hSC hT
  exact TargetWeylProofs.weylConjugationRelations_of_targetLaws hd hT hPU hSC

end Langlands.GroupScheme
