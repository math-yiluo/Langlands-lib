import Langlands.Representation.Classification.SegmentInitialTruncation
import Langlands.Representation.Derivative.GeneralLinearDerivativeDeterminantTwistProof
import Langlands.Representation.Derivative.LevelCalculus

/-!
# Level sequences of multisegments and iterated derivative chains

For a multisegment `a`, `levelSequence a` lists the numbers
`λ_j(a) = ∑_{Δ ∈ a, j < length Δ} rank Δ` for `j < max length`. Its head is the
total rank and its tail is the level sequence of `a⁻`. The predicate
`DerivativeChain T ψ s n W` asserts that the successive derivatives of `W` of the
orders listed by `s` are all defined and that the last one is nonzero. It is
invariant under isomorphism and under real determinant twists.
-/

noncomputable section

open CategoryTheory

namespace Langlands.Derivative.HighestDerivativeChain

open GeneralLinear HarmonicAnalysis PadicField.TopologicalData

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

/-! ## The level sequence of a multisegment -/

section Combinatorics

/-- `levelAt j a = ∑_{Δ ∈ a, j < length Δ} rank Δ`. -/
def levelAt (j : ℕ) (a : T.Multisegment.{uV, uF}) : ℕ :=
  (a.map fun Δ => if j < Δ.length then Δ.rank else 0).sum

/-- The largest length of a segment of `a`, and `0` for the empty multisegment. -/
def maxLength (a : T.Multisegment.{uV, uF}) : ℕ :=
  (a.map Segment.length).sup

/-- The level sequence `(λ_0(a), …, λ_(m-1)(a))`, with `m` the largest length. -/
def levelSequence (a : T.Multisegment.{uV, uF}) : List ℕ :=
  (List.range (maxLength a)).map fun j => levelAt j a

theorem levelAt_cons (j : ℕ) (Δ : T.Segment.{uV, uF}) (a : T.Multisegment.{uV, uF}) :
    levelAt j (Δ ::ₘ a) = (if j < Δ.length then Δ.rank else 0) + levelAt j a := by
  simp [levelAt]

theorem maxLength_cons (Δ : T.Segment.{uV, uF}) (a : T.Multisegment.{uV, uF}) :
    maxLength (Δ ::ₘ a) = max Δ.length (maxLength a) := by
  simp [maxLength]

theorem levelAt_dropLast (j : ℕ) (a : T.Multisegment.{uV, uF}) :
    levelAt j (a.filterMap Segment.dropLast) = levelAt (j + 1) a := by
  induction a using Multiset.induction_on with
  | empty => simp [levelAt]
  | cons Δ a ih =>
    by_cases h : 1 < Δ.length
    · rw [Multiset.filterMap_cons_some _ _ _ (Δ.dropLast_of_one_lt h), levelAt_cons,
        levelAt_cons, ih]
      simp only [Segment.dropLastNonempty_length, Segment.dropLastNonempty_rank]
      have hiff : j < Δ.length - 1 ↔ j + 1 < Δ.length := by omega
      simp only [hiff]
    · have hl : Δ.length = 1 := by have := Δ.length_pos; omega
      rw [Multiset.filterMap_cons_none _ _ (Δ.dropLast_of_length_eq_one hl), levelAt_cons, ih,
        hl]
      simp

theorem maxLength_dropLast (a : T.Multisegment.{uV, uF}) :
    maxLength (a.filterMap Segment.dropLast) = maxLength a - 1 := by
  induction a using Multiset.induction_on with
  | empty => simp [maxLength]
  | cons Δ a ih =>
    by_cases h : 1 < Δ.length
    · rw [Multiset.filterMap_cons_some _ _ _ (Δ.dropLast_of_one_lt h), maxLength_cons,
        maxLength_cons, ih, Segment.dropLastNonempty_length]
      omega
    · have hl : Δ.length = 1 := by have := Δ.length_pos; omega
      rw [Multiset.filterMap_cons_none _ _ (Δ.dropLast_of_length_eq_one hl), maxLength_cons, ih,
        hl]
      omega

theorem levelAt_zero (a : T.Multisegment.{uV, uF}) :
    levelAt 0 a = (a.map Segment.rank).sum := by
  unfold levelAt
  congr 1
  apply Multiset.map_congr rfl
  intro Δ _
  simp [Δ.length_pos]

theorem maxLength_pos {a : T.Multisegment.{uV, uF}} (h : a ≠ 0) : 0 < maxLength a := by
  obtain ⟨Δ, hΔ⟩ := Multiset.exists_mem_of_ne_zero h
  exact lt_of_lt_of_le Δ.length_pos (Multiset.le_sup (Multiset.mem_map_of_mem _ hΔ))

/-- The level sequence of a nonempty multisegment is its total rank followed by the
level sequence of `a⁻`. -/
theorem levelSequence_eq_cons {a : T.Multisegment.{uV, uF}} (h : a ≠ 0) :
    levelSequence a =
      (a.map Segment.rank).sum :: levelSequence (a.filterMap Segment.dropLast) := by
  unfold levelSequence
  rw [maxLength_dropLast]
  obtain ⟨m, hm⟩ : ∃ m, maxLength a = m + 1 := ⟨maxLength a - 1, by
    have := maxLength_pos h; omega⟩
  rw [hm, List.range_succ_eq_map, List.map_cons, List.map_map, levelAt_zero,
    Nat.add_sub_cancel]
  congr 1
  apply List.map_congr_left
  intro j _
  simp [levelAt_dropLast]

@[simp]
theorem levelSequence_zero : levelSequence (0 : T.Multisegment.{uV, uF}) = [] := by
  simp [levelSequence, maxLength]

/-- Maps of segments preserving lengths and ranks preserve the level sequence. -/
theorem levelSequence_map (f : T.Segment.{uV, uF} → T.Segment.{uV, uF})
    (hl : ∀ Δ, (f Δ).length = Δ.length) (hr : ∀ Δ, (f Δ).rank = Δ.rank)
    (a : T.Multisegment.{uV, uF}) : levelSequence (a.map f) = levelSequence a := by
  have h1 : ∀ j, levelAt j (a.map f) = levelAt j a := by
    intro j
    simp [levelAt, Multiset.map_map, hl, hr]
  have h2 : maxLength (a.map f) = maxLength a := by
    simp [maxLength, Multiset.map_map, hl]
  simp [levelSequence, h1, h2]

end Combinatorics

/-! ## Iterated derivative chains -/

section Chain

/-- `DerivativeChain T ψ [k₁, …, k_r] n W`: the derivatives of `W` of orders
`k₁, k₂, …, k_r` can be taken successively (each order positive and at most the
current rank), and the final derivative is nonzero. -/
def DerivativeChain (T : F.TopologicalData)
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) :
    List ℕ → (n : ℕ) →
      (letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)) → Prop
  | [], _, W => Nontrivial W
  | k :: s, n, W => ∃ hk : 0 < k ∧ k ≤ n,
      DerivativeChain T ψ s (n - k)
        (letI := T.topology; (generalLinearDerivative.{uF, uV} T ψ n k hk.2).obj W)

variable (T) (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)

theorem derivativeChain_nil {n : ℕ}
    (W : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)) :
    DerivativeChain T ψ [] n W ↔ Nontrivial W := Iff.rfl

theorem derivativeChain_cons (k : ℕ) (s : List ℕ) {n : ℕ}
    (W : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)) :
    DerivativeChain T ψ (k :: s) n W ↔ ∃ hk : 0 < k ∧ k ≤ n,
      DerivativeChain T ψ s (n - k)
        (letI := T.topology; (generalLinearDerivative.{uF, uV} T ψ n k hk.2).obj W) :=
  Iff.rfl

/-- Derivative chains are invariant under isomorphism. -/
theorem derivativeChain_iff_of_iso (s : List ℕ) :
    letI := T.topology
    ∀ {n : ℕ} {A B : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)} (_ : A ≅ B),
      DerivativeChain T ψ s n A ↔ DerivativeChain T ψ s n B := by
  let := T.topology
  induction s with
  | nil =>
    intro n A B e
    exact LevelCalculus.nontrivial_iff_of_iso e
  | cons k s ih =>
    intro n A B e
    rw [derivativeChain_cons, derivativeChain_cons]
    exact exists_congr fun hk => ih ((generalLinearDerivative.{uF, uV} T ψ n k hk.2).mapIso e)

/-- Derivative chains are invariant under real determinant twists. -/
theorem derivativeChain_twist_iff {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (t : ℝ) (s : List ℕ) :
    letI := T.topology
    ∀ {n : ℕ} (A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)),
      DerivativeChain T ψ s n
          (A.twist (T.determinantPowerCharacter n t) (T.isOpen_ker_determinantPowerCharacter n t)) ↔
        DerivativeChain T ψ s n A := by
  let := T.topology
  induction s with
  | nil =>
    intro n A
    exact Iff.rfl
  | cons k s ih =>
    intro n A
    rw [derivativeChain_cons, derivativeChain_cons]
    refine exists_congr fun hk => ?_
    obtain ⟨e⟩ := generalLinearDerivativeDeterminantTwist.{uF, uV} F T ψ n k hk.2 t
    exact (derivativeChain_iff_of_iso T ψ s (e.app A)).trans (ih _)

end Chain

end Langlands.Derivative.HighestDerivativeChain
