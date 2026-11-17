import Langlands.GroupScheme.Reductive.LocalSplitWeylBraid

/-! # Rank-two chains of simple reflections and common rescalings along them -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

namespace LocalSplitCell

section Numeric

set_option linter.unusedSimpArgs false

/-- Numerical data of a root `g` relative to a root `α` and two simple roots `c`, `j`: the
height `h`, the pairings `x = ⟨g, c^∨⟩`, `y = ⟨g, j^∨⟩`, and the coefficients `a`, `b` with
`g = α + a c + b j`. -/
structure RankTwoState where
  h : ℤ
  x : ℤ
  y : ℤ
  a : ℤ
  b : ℤ

/-- The effect of `s_c` (letter `true`) or `s_j` (letter `false`) on the numerical data, for
`A = -⟨c, j^∨⟩` and `B = -⟨j, c^∨⟩`. -/
def RankTwoState.step (A B : ℤ) : Bool → RankTwoState → RankTwoState
  | true, s => ⟨s.h - s.x, -s.x, s.y + A * s.x, s.a - s.x, s.b⟩
  | false, s => ⟨s.h - s.y, s.x + B * s.y, -s.y, s.a, s.b - s.y⟩

/-- The numerical data after a list of letters, the head applied first. -/
def RankTwoState.run (A B : ℤ) (l : List Bool) (s : RankTwoState) : RankTwoState :=
  l.foldl (fun s t => RankTwoState.step A B t s) s

/-- **Admissible chains.** Each step either stays strictly below height `p`, or is the step
`s_j` at the starting root (`a = b = 0`). -/
def RankTwoState.Admissible (A B p : ℤ) : List Bool → RankTwoState → Prop
  | [], _ => True
  | t :: l, s => ((s.h < p ∧ (RankTwoState.step A B t s).h < p) ∨
      (t = false ∧ s.a = 0 ∧ s.b = 0)) ∧ RankTwoState.Admissible A B p l (RankTwoState.step A B t s)

/-- The alternating list of letters of length `n` starting with `t`. -/
def altLetters : Bool → ℕ → List Bool
  | _, 0 => []
  | t, n + 1 => t :: altLetters (!t) n

/-- The starting data of a root of height `p` with pairings `x`, `y`. -/
def RankTwoState.start (p x y : ℤ) : RankTwoState := ⟨p, x, y, 0, 0⟩

/-- **The two alternating chains of a dihedral group of order `2m`.** Starting at a root with
pairings `x ≥ 0`, `y > 0`, the chain `s_c` followed by the alternating chain of length `m - 1`
starting with `s_j`, and the alternating chain of length `m` starting with `s_j`, are
admissible and end at the same root. -/
def TwoChains (A B : ℤ) (m : ℕ) : Prop :=
  ∀ p x y : ℤ, 0 ≤ x → 0 < y →
    RankTwoState.Admissible A B p (altLetters false (m - 1))
        (RankTwoState.step A B true (RankTwoState.start p x y)) ∧
      RankTwoState.Admissible A B p (altLetters false m) (RankTwoState.start p x y) ∧
      (RankTwoState.run A B (altLetters false (m - 1))
          (RankTwoState.step A B true (RankTwoState.start p x y))).a =
        (RankTwoState.run A B (altLetters false m) (RankTwoState.start p x y)).a ∧
      (RankTwoState.run A B (altLetters false (m - 1))
          (RankTwoState.step A B true (RankTwoState.start p x y))).b =
        (RankTwoState.run A B (altLetters false m) (RankTwoState.start p x y)).b

theorem twoChains_a1a1 : TwoChains 0 0 2 := by
  intro p x y hx hy
  simp only [altLetters, RankTwoState.Admissible, RankTwoState.run, RankTwoState.start,
    RankTwoState.step, List.foldl, Bool.not_false, Bool.not_true, true_and, and_true,
    Bool.true_eq_false, false_and, or_false, or_true, true_or, false_or, and_self]
  rcases eq_or_lt_of_le hx with h0 | h0
  · subst h0
    simp only [sub_zero, neg_zero, zero_mul, mul_zero, add_zero, zero_add, lt_self_iff_false,
      false_and, false_or, or_false, true_and, and_true, true_or, or_true, and_self]
    omega
  · omega

theorem twoChains_a2 : TwoChains 1 1 3 := by
  intro p x y hx hy
  simp only [altLetters, RankTwoState.Admissible, RankTwoState.run, RankTwoState.start,
    RankTwoState.step, List.foldl, Bool.not_false, Bool.not_true, true_and, and_true,
    Bool.true_eq_false, false_and, or_false, or_true, true_or, false_or, and_self]
  rcases eq_or_lt_of_le hx with h0 | h0
  · subst h0
    simp only [sub_zero, neg_zero, zero_mul, mul_zero, add_zero, zero_add, lt_self_iff_false,
      false_and, false_or, or_false, true_and, and_true, true_or, or_true, and_self]
    omega
  · omega

theorem twoChains_b2 : TwoChains 1 2 4 := by
  intro p x y hx hy
  simp only [altLetters, RankTwoState.Admissible, RankTwoState.run, RankTwoState.start,
    RankTwoState.step, List.foldl, Bool.not_false, Bool.not_true, true_and, and_true,
    Bool.true_eq_false, false_and, or_false, or_true, true_or, false_or, and_self]
  rcases eq_or_lt_of_le hx with h0 | h0
  · subst h0
    simp only [sub_zero, neg_zero, zero_mul, mul_zero, add_zero, zero_add, lt_self_iff_false,
      false_and, false_or, or_false, true_and, and_true, true_or, or_true, and_self]
    omega
  · omega

theorem twoChains_b2' : TwoChains 2 1 4 := by
  intro p x y hx hy
  simp only [altLetters, RankTwoState.Admissible, RankTwoState.run, RankTwoState.start,
    RankTwoState.step, List.foldl, Bool.not_false, Bool.not_true, true_and, and_true,
    Bool.true_eq_false, false_and, or_false, or_true, true_or, false_or, and_self]
  rcases eq_or_lt_of_le hx with h0 | h0
  · subst h0
    simp only [sub_zero, neg_zero, zero_mul, mul_zero, add_zero, zero_add, lt_self_iff_false,
      false_and, false_or, or_false, true_and, and_true, true_or, or_true, and_self]
    omega
  · omega

theorem twoChains_g2 : TwoChains 1 3 6 := by
  intro p x y hx hy
  simp only [altLetters, RankTwoState.Admissible, RankTwoState.run, RankTwoState.start,
    RankTwoState.step, List.foldl, Bool.not_false, Bool.not_true, true_and, and_true,
    Bool.true_eq_false, false_and, or_false, or_true, true_or, false_or, and_self]
  rcases eq_or_lt_of_le hx with h0 | h0
  · subst h0
    simp only [sub_zero, neg_zero, zero_mul, mul_zero, add_zero, zero_add, lt_self_iff_false,
      false_and, false_or, or_false, true_and, and_true, true_or, or_true, and_self]
    omega
  · omega

theorem twoChains_g2' : TwoChains 3 1 6 := by
  intro p x y hx hy
  simp only [altLetters, RankTwoState.Admissible, RankTwoState.run, RankTwoState.start,
    RankTwoState.step, List.foldl, Bool.not_false, Bool.not_true, true_and, and_true,
    Bool.true_eq_false, false_and, or_false, or_true, true_or, false_or, and_self]
  rcases eq_or_lt_of_le hx with h0 | h0
  · subst h0
    simp only [sub_zero, neg_zero, zero_mul, mul_zero, add_zero, zero_add, lt_self_iff_false,
      false_and, false_or, or_false, true_and, and_true, true_or, or_true, and_self]
    omega
  · omega

end Numeric

section Roots

variable {I J : Type u} {P : RootDatum J (I → ℤ) (I → ℤ)}

/-- The simple root named by a letter: `c` for `true`, `j` for `false`. -/
def letter (c j : J) : Bool → J
  | true => c
  | false => j

theorem pairing_of_root_eq {g δ ε : J} {z : ℤ} (h : P.root g = P.root δ + z • P.root ε)
    (k : J) : P.pairing g k = P.pairing δ k + z * P.pairing ε k := by
  rw [← RootPairing.root_coroot_eq_pairing, h]
  simp only [map_add, map_zsmul, LinearMap.add_apply, LinearMap.smul_apply,
    RootPairing.root_coroot_eq_pairing, smul_eq_mul]

theorem root_reflectionPerm_eq (k g : J) :
    P.root (P.reflectionPerm k g) = P.root g + (-P.pairing g k) • P.root k := by
  rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_root, neg_smul,
    sub_eq_add_neg]

/-- The numerical data `s` describe the root `g` relative to `α`, `c`, `j`. -/
def IsRankTwoState (b : P.Base) (α c j g : J) (s : RankTwoState) : Prop :=
  P.root g = P.root α + s.a • P.root c + s.b • P.root j ∧ b.height g = s.h ∧
    P.pairing g c = s.x ∧ P.pairing g j = s.y

theorem isRankTwoState_start (b : P.Base) (α c j : J) :
    IsRankTwoState b α c j α
      (RankTwoState.start (b.height α) (P.pairing α c) (P.pairing α j)) := by
  refine ⟨?_, rfl, rfl, rfl⟩
  simp only [RankTwoState.start, zero_smul, add_zero]

theorem IsRankTwoState.step {b : P.Base} {α c j : J} (hc : c ∈ b.support) (hj : j ∈ b.support)
    {g : J} {s : RankTwoState} (h : IsRankTwoState b α c j g s) (t : Bool) :
    IsRankTwoState b α c j (P.reflectionPerm (letter c j t) g)
      (RankTwoState.step (-P.pairing c j) (-P.pairing j c) t s) := by
  obtain ⟨hr, hh, hx, hy⟩ := h
  cases t with
  | true =>
    simp only [letter, RankTwoState.step]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [root_reflectionPerm_eq, hr, hx]
      module
    · rw [height_reflectionPerm_of_mem P hc, hh, hx]
    · rw [pairing_of_root_eq (root_reflectionPerm_eq c g), hx, RootPairing.pairing_same]
      ring
    · rw [pairing_of_root_eq (root_reflectionPerm_eq c g), hx, hy]
      ring
  | false =>
    simp only [letter, RankTwoState.step]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [root_reflectionPerm_eq, hr, hy]
      module
    · rw [height_reflectionPerm_of_mem P hj, hh, hy]
    · rw [pairing_of_root_eq (root_reflectionPerm_eq j g), hx, hy]
      ring
    · rw [pairing_of_root_eq (root_reflectionPerm_eq j g), hy, RootPairing.pairing_same]
      ring

theorem wordPerm_reverse_cons (k : J) (l : List J) (g : J) :
    Langlands.LinearAlgebra.wordPerm P (k :: l).reverse g =
      Langlands.LinearAlgebra.wordPerm P l.reverse (P.reflectionPerm k g) := by
  rw [List.reverse_cons, wordPerm_append]
  rfl

theorem IsRankTwoState.run {b : P.Base} {α c j : J} (hc : c ∈ b.support) (hj : j ∈ b.support) :
    ∀ (l : List Bool) {g : J} {s : RankTwoState}, IsRankTwoState b α c j g s →
      IsRankTwoState b α c j
        (Langlands.LinearAlgebra.wordPerm P (l.map (letter c j)).reverse g)
        (RankTwoState.run (-P.pairing c j) (-P.pairing j c) l s)
  | [], _, _, h => h
  | t :: l, g, s, h => by
    rw [List.map_cons, wordPerm_reverse_cons]
    exact IsRankTwoState.run hc hj l (h.step hc hj t)

/-- Roots `α + a c + b j` with `α` outside the span of `c` and `j` are neither `c` nor `j`. -/
theorem IsRankTwoState.not_mem_span {b : P.Base} {α c j g : J} {s : RankTwoState}
    (h : IsRankTwoState b α c j g s)
    (hspan : ∀ x y : ℤ, P.root α ≠ x • P.root c + y • P.root j) :
    ∀ x y : ℤ, P.root g ≠ x • P.root c + y • P.root j := by
  intro x y hxy
  apply hspan (x - s.a) (y - s.b)
  have h₁ := h.1
  rw [hxy] at h₁
  have h₂ : P.root α = x • P.root c + y • P.root j - s.a • P.root c - s.b • P.root j := by
    rw [h₁]
    abel
  rw [h₂]
  module

theorem ne_of_not_mem_span {c j g : J} (hspan : ∀ x y : ℤ, P.root g ≠ x • P.root c + y • P.root j)
    (t : Bool) : g ≠ letter c j t := by
  rintro rfl
  cases t with
  | true => exact hspan 1 0 (by simp [letter])
  | false => exact hspan 0 1 (by simp [letter])

end Roots

section Chains

variable {R : Type u} [CommRing R] {I : Type u} {J : Type u} [Finite J]
  {G H : GroupScheme (Spec (CommRingCat.of R))} {P : RootDatum J (I → ℤ) (I → ℤ)} [P.IsReduced]
  {u : J → (Ga R ⟶ G)} {u' : J → (Ga R ⟶ H)}

/-- **Common rescalings along admissible chains.** Let `α` be a positive root outside the span
of the simple roots `c`, `j`. Suppose every step `g ↦ s_k g` (`k ∈ {c, j}`) between positive
roots of height below that of `α` has a common rescaling, and so does the step `s_j α ↦ α`.
Then conjugation along an admissible chain from a root `g = α + a c + b j` has a common
rescaling. -/
theorem univRel_chain {b : P.Base} {c j α : J} (hc : c ∈ b.support) (hj : j ∈ b.support)
    (hα : ∀ x y : ℤ, P.root α ≠ x • P.root c + y • P.root j)
    (v : J → (Ga R ⟶ G)) (v' : J → (Ga R ⟶ H))
    (hIH : ∀ (t : Bool) (g : J), b.IsPos g → b.IsPos (P.reflectionPerm (letter c j t) g) →
      b.height g < b.height α → b.height (P.reflectionPerm (letter c j t) g) < b.height α →
      UnivRel P u u' [letter c j t] (v (P.reflectionPerm (letter c j t) g)) (v g)
        (v' (P.reflectionPerm (letter c j t) g)) (v' g))
    (hdef : UnivRel P u u' [j] (v (P.reflectionPerm j α)) (v α) (v' (P.reflectionPerm j α))
      (v' α)) :
    ∀ (l : List Bool) {g : J} {s : RankTwoState}, IsRankTwoState b α c j g s → b.IsPos g →
      RankTwoState.Admissible (-P.pairing c j) (-P.pairing j c) (b.height α) l s →
      UnivRel P u u' (l.map (letter c j))
        (v (Langlands.LinearAlgebra.wordPerm P (l.map (letter c j)).reverse g)) (v g)
        (v' (Langlands.LinearAlgebra.wordPerm P (l.map (letter c j)).reverse g)) (v' g)
  | [], g, s, _, _, _ => UnivRel.refl _ _
  | t :: l, g, s, hs, hg, hadm => by
    obtain ⟨hstep, hrest⟩ := hadm
    have hspan := hs.not_mem_span hα
    have hg' : b.IsPos (P.reflectionPerm (letter c j t) g) :=
      hg.reflectionPerm (by cases t <;> assumption) (ne_of_not_mem_span hspan t)
    have ih := univRel_chain hc hj hα v v' hIH hdef l (hs.step hc hj t) hg' hrest
    have hone : UnivRel P u u' [letter c j t] (v (P.reflectionPerm (letter c j t) g)) (v g)
        (v' (P.reflectionPerm (letter c j t) g)) (v' g) := by
      rcases hstep with ⟨h₁, h₂⟩ | ⟨rfl, ha, hb⟩
      · have e₂ := (hs.step hc hj t).2.1
        rw [← hs.2.1] at h₁
        rw [← e₂] at h₂
        exact hIH t g hg hg' h₁ h₂
      · have : g = α := P.root.injective (by rw [hs.1, ha, hb, zero_smul, zero_smul, add_zero,
          add_zero])
        subst this
        exact hdef
    rw [List.map_cons, wordPerm_reverse_cons]
    exact UnivRel.trans (l₂ := [letter c j t]) ih hone

/-- `altLetters` maps to alternating words. -/
theorem altLetters_succ (t : Bool) (n : ℕ) : altLetters t (n + 1) = t :: altLetters (!t) n := rfl

/-- **The two-path argument.** If the alternating words of length `m` in `c`, `j` starting with
`c` and with `j` conjugate in the same way in both groups (braid relation), the admissible
chains of `TwoChains` give a common rescaling for the step `s_c α ↦ α`. -/
theorem univRel_twoPath {b : P.Base} {c j α : J} (hc : c ∈ b.support) (hj : j ∈ b.support)
    (hαpos : b.IsPos α) (hα : ∀ x y : ℤ, P.root α ≠ x • P.root c + y • P.root j)
    (hx : 0 ≤ P.pairing α c) (hy : 0 < P.pairing α j) {m : ℕ} (hm : 1 ≤ m)
    (hchains : TwoChains (-P.pairing c j) (-P.pairing j c) m)
    (hbG : ∀ w, wordConj P u ((altLetters true m).map (letter c j)) w =
      wordConj P u ((altLetters false m).map (letter c j)) w)
    (hbH : ∀ w, wordConj P u' ((altLetters true m).map (letter c j)) w =
      wordConj P u' ((altLetters false m).map (letter c j)) w)
    (v : J → (Ga R ⟶ G)) (v' : J → (Ga R ⟶ H))
    (hIH : ∀ (t : Bool) (g : J), b.IsPos g → b.IsPos (P.reflectionPerm (letter c j t) g) →
      b.height g < b.height α → b.height (P.reflectionPerm (letter c j t) g) < b.height α →
      UnivRel P u u' [letter c j t] (v (P.reflectionPerm (letter c j t) g)) (v g)
        (v' (P.reflectionPerm (letter c j t) g)) (v' g))
    (hdef : UnivRel P u u' [j] (v (P.reflectionPerm j α)) (v α) (v' (P.reflectionPerm j α))
      (v' α)) :
    UnivRel P u u' [c] (v (P.reflectionPerm c α)) (v α) (v' (P.reflectionPerm c α)) (v' α) := by
  obtain ⟨h₁, h₂, ha, hb⟩ := hchains (b.height α) (P.pairing α c) (P.pairing α j) hx hy
  have hs₀ := isRankTwoState_start b α c j
  have hs₁ : IsRankTwoState b α c j (P.reflectionPerm c α) _ := hs₀.step hc hj true
  have hcpos : b.IsPos (P.reflectionPerm c α) :=
    hαpos.reflectionPerm hc (ne_of_not_mem_span hα true)
  have k₁ := univRel_chain hc hj hα v v' hIH hdef (altLetters false (m - 1)) hs₁ hcpos h₁
  have k₂ := univRel_chain hc hj hα v v' hIH hdef (altLetters false m) hs₀ hαpos h₂
  have e₁ := IsRankTwoState.run hc hj (altLetters false (m - 1)) hs₁
  have e₂ := IsRankTwoState.run hc hj (altLetters false m) hs₀
  have hend : Langlands.LinearAlgebra.wordPerm P
        ((altLetters false (m - 1)).map (letter c j)).reverse (P.reflectionPerm c α) =
      Langlands.LinearAlgebra.wordPerm P ((altLetters false m).map (letter c j)).reverse α := by
    apply P.root.injective
    rw [e₁.1, e₂.1, ha, hb]
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at k₁ hend
  rw [← hend] at k₂
  have k₂' := k₂.congr_word (hbG _).symm (hbH _).symm
  rw [altLetters_succ, List.map_cons, Bool.not_true] at k₂'
  exact UnivRel.cancel (l₁ := (altLetters false m').map (letter c j)) (l₂ := [c]) k₂' k₁

end Chains

section Types

variable {I J : Type u} {P : RootDatum J (I → ℤ) (I → ℤ)}

/-- The braid length: the order of `s_c s_j` when `⟨c, j^∨⟩ ⟨j, c^∨⟩ = n`. -/
def braidLength (n : ℤ) : ℕ := if n = 0 then 2 else if n = 1 then 3 else if n = 2 then 4 else 6

theorem one_le_braidLength (n : ℤ) : 1 ≤ braidLength n := by
  unfold braidLength
  split_ifs <;> norm_num

/-- The Cartan entries of two distinct simple roots. -/
theorem simple_pair_cases [Finite J] [P.IsReduced] {b : P.Base} {c j : J} (hc : c ∈ b.support)
    (hj : j ∈ b.support) (hcj : c ≠ j) :
    (P.pairingIn ℤ c j = 0 ∧ P.pairingIn ℤ j c = 0) ∨
      (P.pairingIn ℤ c j = -1 ∧ P.pairingIn ℤ j c = -1) ∨
      (P.pairingIn ℤ c j = -1 ∧ P.pairingIn ℤ j c = -2) ∨
      (P.pairingIn ℤ c j = -2 ∧ P.pairingIn ℤ j c = -1) ∨
      (P.pairingIn ℤ c j = -1 ∧ P.pairingIn ℤ j c = -3) ∨
      (P.pairingIn ℤ c j = -3 ∧ P.pairingIn ℤ j c = -1) := by
  have hli : LinearIndependent ℤ ![P.root c, P.root j] :=
    b.linearIndependent_pair_of_ne (i := ⟨c, hc⟩) (j := ⟨j, hj⟩)
      (fun h' => hcj (congrArg Subtype.val h'))
  have hr1 : P.root c ≠ P.root j := fun h => hcj (P.root.injective h)
  have hr2 : P.root c ≠ -P.root j := by
    intro h
    have := LinearIndependent.pair_iff.mp hli 1 1 (by rw [h]; module)
    simp at this
  have hle1 : P.pairingIn ℤ c j ≤ 0 := b.pairingIn_le_zero_of_ne hcj hc hj
  have hle2 : P.pairingIn ℤ j c ≤ 0 := b.pairingIn_le_zero_of_ne hcj.symm hj hc
  have hmem := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed' c j hr1 hr2
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
  omega

theorem twoChains_of_cases {c j : J}
    (h : (P.pairingIn ℤ c j = 0 ∧ P.pairingIn ℤ j c = 0) ∨
      (P.pairingIn ℤ c j = -1 ∧ P.pairingIn ℤ j c = -1) ∨
      (P.pairingIn ℤ c j = -1 ∧ P.pairingIn ℤ j c = -2) ∨
      (P.pairingIn ℤ c j = -2 ∧ P.pairingIn ℤ j c = -1) ∨
      (P.pairingIn ℤ c j = -1 ∧ P.pairingIn ℤ j c = -3) ∨
      (P.pairingIn ℤ c j = -3 ∧ P.pairingIn ℤ j c = -1)) :
    TwoChains (-P.pairing c j) (-P.pairing j c)
      (braidLength (P.pairingIn ℤ c j * P.pairingIn ℤ j c)) := by
  rw [← pairingIn_eq_pairing, ← pairingIn_eq_pairing]
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rw [h1, h2] <;> norm_num [braidLength]
  · exact twoChains_a1a1
  · exact twoChains_a2
  · exact twoChains_b2
  · exact twoChains_b2'
  · exact twoChains_g2
  · exact twoChains_g2'

end Types

section Positive

open Langlands.LinearAlgebra (a1a1_coeffs a2_coeffs b2_coeffs g2_coeffs)

variable {R : Type u} [CommRing R] [IsLocalRing R] {I : Type u} [Fintype I] [DecidableEq I]
  {J : Type u} {G H : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  [IsAffineHom H.X.hom] {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {i' : splitTorus (Spec (CommRingCat.of R)) I ⟶ H} {P : RootDatum J (I → ℤ) (I → ℤ)}
  {b : P.Base} {W : ∀ α, SimpleWord P b α} {u : J → (Ga R ⟶ G)} {u' : J → (Ga R ⟶ H)}

variable (P b) in
/-- **Braid relations as conjugations.** For distinct simple roots `c`, `j`, conjugation along
the alternating words of the braid length starting with `c` and with `j` agree. -/
def WordBraids {G : GroupScheme (Spec (CommRingCat.of R))} (u : J → (Ga R ⟶ G)) : Prop :=
  ∀ c ∈ b.support, ∀ j ∈ b.support, c ≠ j → ∀ w : Ga R ⟶ G,
    wordConj P u ((altLetters true (braidLength (P.pairingIn ℤ c j * P.pairingIn ℤ j c))).map
        (letter c j)) w =
      wordConj P u ((altLetters false (braidLength (P.pairingIn ℤ c j * P.pairingIn ℤ j c))).map
        (letter c j)) w

omit [IsLocalRing R] [Fintype I] [DecidableEq I] [IsAffineHom G.X.hom] in
/-- The Weyl family along a descending letter. -/
theorem weylFamily_descend {G : GroupScheme (Spec (CommRingCat.of R))} {u : J → (Ga R ⟶ G)}
    {α j : J} (hsimple : (W α).simple = (W (P.reflectionPerm j α)).simple)
    (hword : (W α).word = j :: (W (P.reflectionPerm j α)).word) :
    wordConj P u [j] (weylFamily P W u (P.reflectionPerm j α)) = weylFamily P W u α := by
  unfold weylFamily
  rw [hword, hsimple]
  rfl

/-- **A root in the span of its descending letter and `c`.** -/
theorem univRel_top_span (hdG : IsNormalSimpleData i P b W u)
    (hdH : IsNormalSimpleData i' P b W u') {c j α : J} (hc : c ∈ b.support)
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
      (hdH.wordConj_fix_of_coeffs hc hj hcj (hdH.isRootParametrization α) h0 hβ hΦ ho₁ hn₁ ho₂
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
      · rw [hdH.weylFamily_simple hj, hdH.wordConj_a2 hc hj hcj h1 h2,
          ← hdH.weylFamily_simple hc, hdefH]
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
      · rw [← hdefH, hdH.weylFamily_simple hc, hdH.wordConj_b2 hc hj hcj h1 h2]
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
theorem univRel_top (hdG : IsNormalSimpleData i P b W u) (hdH : IsNormalSimpleData i' P b W u')
    (hbG : WordBraids P b u) (hbH : WordBraids P b u') {c : J} (hc : c ∈ b.support) {α : J}
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
        (hdH.wordConj_fix_of_coeffs hc hαs hcα' (hdH.isRootParametrization α) h0 hβ
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
        exact univRel_top_span hdG hdH hc hj hcj hα hαs hx hpj hxy hdefG hdefH
      · push Not at hspan
        exact univRel_twoPath hc hj hα hspan hx hpj (one_le_braidLength _)
          (twoChains_of_cases (simple_pair_cases hc hj hcj)) (hbG c hc j hj hcj)
          (hbH c hc j hj hcj) _ _
          (fun t g h₁ h₂ h₃ h₄ => hIH _ (by cases t <;> assumption) g h₁ h₂ h₃ h₄)
          (UnivRel.of_eq hdefG hdefH)

/-- **Common rescalings between positive roots.** For every simple root `c` and positive
roots `α`, `s_c α`, the step `s_c α ↦ α` has a common rescaling. -/
theorem univRel_positive (hdG : IsNormalSimpleData i P b W u)
    (hdH : IsNormalSimpleData i' P b W u') (hbG : WordBraids P b u) (hbH : WordBraids P b u') :
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
    · exact univRel_top hdG hdH hbG hbH hc hα hcα hx (hIH α h₁ hα)
    · have hββ : P.reflectionPerm c (P.reflectionPerm c α) = α :=
        RootPairing.reflectionPerm_self _ _ _
      have hxβ : 0 ≤ P.pairing (P.reflectionPerm c α) c := by
        rw [pairing_of_root_eq (root_reflectionPerm_eq c α), RootPairing.pairing_same]
        omega
      have key := univRel_top hdG hdH hbG hbH hc hcα (by rw [hββ]; exact hα) hxβ
        (hIH _ h₂ hcα)
      rw [hββ] at key
      exact UnivRel.inv_of_param hdG hdH hc (hdG.isRootParametrization α)
        (hdH.isRootParametrization α) key

end Positive

section Final

variable {R : Type u} [CommRing R] [IsLocalRing R] {I : Type u} [Fintype I] [DecidableEq I]
  {J : Type u} {G H : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  [IsAffineHom H.X.hom] {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {i' : splitTorus (Spec (CommRingCat.of R)) I ⟶ H} {P : RootDatum J (I → ℤ) (I → ℤ)}
  {b : P.Base} {W : ∀ α, SimpleWord P b α} {u : J → (Ga R ⟶ G)} {u' : J → (Ga R ⟶ H)}

omit [IsLocalRing R] [Fintype I] [DecidableEq I] [IsAffineHom G.X.hom] [IsAffineHom H.X.hom] in
theorem wordPerm_eq_of_root {l : List J} {k k' : J}
    (h : wordReflect P l (P.root k) = P.root k') : Langlands.LinearAlgebra.wordPerm P l k = k' :=
  P.root.injective (by rw [Langlands.LinearAlgebra.root_wordPerm, h])

/-- **Braid relations of the simple Weyl points**, from partner uniqueness. -/
theorem wordBraids_of_partnerUnique (hd : IsNormalSimpleData i P b W u)
    (hPU : PartnerUnique P G i) : WordBraids P b u := by
  classical
  have := hd.rootDatum.finite
  have : P.IsReduced := hd.rootDatum.isReduced
  intro c hc j hj hcj w
  apply wordConj_congr_of_wordBase
  have hcs : ∀ x ∈ [c], x ∈ b.support := by simpa using hc
  rcases simple_pair_cases hc hj hcj with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
    rw [h1, h2] <;> norm_num [braidLength, altLetters, letter]
  · have hfix := hd.wordConj_fix_of_coeffs hc hj hcj (hd.param j hj).1 h2
      (m := 0) (n := 1) (by module)
      (fun g m n h => Langlands.LinearAlgebra.a1a1_coeffs hc hj hcj h2 h) (by omega)
      (fun dS dT h₁ h₂ h => by omega) (by omega) (fun dS dT h₁ h₂ h => by omega)
    have hroot : Langlands.LinearAlgebra.wordPerm P [c] j = j := wordPerm_eq_of_root (by
      simp only [wordReflect, List.foldr, RootPairing.reflection_apply_root,
        pairing_eq_of_pairingIn h2, zero_smul, sub_zero])
    simpa using hd.wordBase_braid hPU hcs hj hj hroot hfix
  · have hroot : Langlands.LinearAlgebra.wordPerm P [c, j] c = j := wordPerm_eq_of_root (by
      simp only [wordReflect, List.foldr, RootPairing.reflection_apply_root, map_sub, map_smul,
        RootPairing.pairing_same, pairing_eq_of_pairingIn h1,
        pairing_eq_of_pairingIn h2]
      module)
    simpa using hd.wordBase_braid hPU (l := [c, j]) (by simp [hc, hj]) hc hj hroot
      (hd.conj_a2 hc hj hcj h1 h2)
  · have hroot : Langlands.LinearAlgebra.wordPerm P [c, j, c] j = j := wordPerm_eq_of_root (by
      simp only [wordReflect, List.foldr, RootPairing.reflection_apply_root, map_sub, map_smul,
        RootPairing.pairing_same, pairing_eq_of_pairingIn h1,
        pairing_eq_of_pairingIn h2]
      module)
    simpa using hd.wordBase_braid hPU (l := [c, j, c]) (by simp [hc, hj]) hj hj hroot
      (hd.conj_b2 hc hj hcj h1 h2)
  · have hroot : Langlands.LinearAlgebra.wordPerm P [j, c, j] c = c := wordPerm_eq_of_root (by
      simp only [wordReflect, List.foldr, RootPairing.reflection_apply_root, map_sub, map_smul,
        RootPairing.pairing_same, pairing_eq_of_pairingIn h1,
        pairing_eq_of_pairingIn h2]
      module)
    have key := hd.wordBase_braid hPU (l := [j, c, j]) (by simp [hc, hj]) hc hc hroot
      (hd.conj_b2 hj hc hcj.symm h2 h1)
    simp only [List.cons_append, List.nil_append] at key
    exact key.symm
  · have hroot : Langlands.LinearAlgebra.wordPerm P [c, j, c, j, c] j = j :=
      wordPerm_eq_of_root (by
        simp only [wordReflect, List.foldr, RootPairing.reflection_apply_root, map_sub, map_smul,
          RootPairing.pairing_same,
          pairing_eq_of_pairingIn h1, pairing_eq_of_pairingIn h2]
        module)
    simpa using hd.wordBase_braid hPU (l := [c, j, c, j, c]) (by simp [hc, hj]) hj hj hroot
      (hd.conj_g2 hc hj hcj h1 h2)
  · have hroot : Langlands.LinearAlgebra.wordPerm P [j, c, j, c, j] c = c :=
      wordPerm_eq_of_root (by
        simp only [wordReflect, List.foldr, RootPairing.reflection_apply_root, map_sub, map_smul,
          RootPairing.pairing_same,
          pairing_eq_of_pairingIn h1, pairing_eq_of_pairingIn h2]
        module)
    have key := hd.wordBase_braid hPU (l := [j, c, j, c, j]) (by simp [hc, hj]) hc hc hroot
      (hd.conj_g2 hj hc hcj.symm h2 h1)
    simp only [List.cons_append, List.nil_append] at key
    exact key.symm

/-- The simple Weyl point carries `v_c = u_c` to `v_{-c}`. -/
theorem IsNormalSimpleData.wordConj_weylFamily_simple
    (hd : IsNormalSimpleData i P b W u) {c : J} (hc : c ∈ b.support) :
    wordConj P u [c] (weylFamily P W u c) = weylFamily P W u (P.reflectionPerm c c) := by
  rw [hd.weylFamily_simple hc, hd.wordConj_simple_self hc,
    hd.weylFamily_neg (RootPairing.Base.isPos_of_mem_support hc)]
  unfold oppositeFamily
  rw [(hd.words.1 c hc).1, (hd.words.1 c hc).2]
  rfl

/-- **Common Weyl conjugation units**, from partner uniqueness and inverse rescaling in both
groups. -/
theorem weylConjugationRelations_of_partner (hdG : IsNormalSimpleData i P b W u)
    (hdH : IsNormalSimpleData i' P b W u') (hPUG : PartnerUnique P G i)
    (hPUH : PartnerUnique P H i') (hSCG : PartnerRescales P G i)
    (hSCH : PartnerRescales P H i') : WeylConjugationRelations P b W u u' := by
  classical
  have := hdG.rootDatum.finite
  have : P.IsReduced := hdG.rootDatum.isReduced
  have hbG := wordBraids_of_partnerUnique hdG hPUG
  have hbH := wordBraids_of_partnerUnique hdH hPUH
  intro c hc d
  have hpos : ∀ {α : J}, b.IsPos α → α ≠ c →
      UnivRel P u u' [c] (weylFamily P W u α) (weylFamily P W u (P.reflectionPerm c α))
        (weylFamily P W u' α) (weylFamily P W u' (P.reflectionPerm c α)) := by
    intro α hα hαc
    have hcα : b.IsPos (P.reflectionPerm c α) := hα.reflectionPerm hc hαc
    have key := univRel_positive hdG hdH hbG hbH
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
        exact hdH.wordConj_weylFamily_simple hc
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
        rw [← hdH.wordConj_weylFamily_simple hc, RootPairing.reflectionPerm_self, Units.val_one,
          scaleHom_one, Category.id_comp]
        change wordConj P u' [α, α] (weylFamily P W u' α) = _
        rw [wordConj_sq hdH.rootDatum (hdH.rankOne α hc) (hdH.isRootParametrization α),
          RootPairing.pairingIn_same, signUnit_even ⟨1, by norm_num⟩, Units.val_one, scaleHom_one,
          Category.id_comp]
    · obtain ⟨κ, e₁, e₂⟩ := hpos hα hαc
      have hcα : b.IsPos (P.reflectionPerm c α) := hα.reflectionPerm hc hαc
      exact ⟨κ⁻¹, hdG.conj_neg hPUG hSCG hc hα hcα e₁, hdH.conj_neg hPUH hSCH hc hα hcα e₂⟩

end Final

end LocalSplitCell

end Langlands.GroupScheme
