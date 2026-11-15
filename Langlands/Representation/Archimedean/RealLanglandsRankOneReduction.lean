import Langlands.Representation.Archimedean.RealLanglandsQuotientReduction

/-!
# Reduction of the real Langlands classification to a rank-one step

`RealLanglandsFromPrincipalSeriesStatement` asks that an irreducible admissible
`(𝔤𝔩_n(ℝ), O(n))`-module which receives a nonzero intertwiner from a principal series also
receives one from the standard module of a list of real blocks in Langlands order. This file
reduces it to one local statement about two adjacent blocks,
`RealRankOneStepStatement`: if the module receives a nonzero intertwiner from the standard
module of a list of blocks in which a block `x` is immediately followed by a block `y` with
`Re t(x) < Re t(y)`, then either it receives one after exchanging `x` and `y`, or it receives
one after replacing the pair `x, y` by a list of blocks with the same exponent support (the
same infinitesimal character on the Levi factor `GL_{r(x) + r(y)}(ℝ)`) and a strictly larger
sum of squared weights.

`realLanglandsFromPrincipalSeries_of_rankOneStep` proves the reduction by repeating the step.
The exponent support stays that of the principal series; the sum of squared weights is
bounded in terms of that support, and it never decreases; when it stays fixed the step is an
exchange, which removes one inversion. A list with no adjacent inversion is in Langlands
order.
-/

noncomputable section

open scoped TensorProduct Matrix

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean

-- As in `GKModule`: the charts on units need reduction through the normed-ring instances of
-- matrices.
set_option backward.isDefEq.respectTransparency false

universe uV

/-! ## Exponent support and weights of real blocks -/

/-- The exponent support of a real block: the list of exponents `s` of the characters
`|·|^s` (up to sign characters) at its diagonal positions. The character `sgn^ε |·|^t`
contributes `[t]`; the real induction of `(z/|z|)^m |z|^(2t)` contributes
`[t + |m|/2, t - |m|/2]`, the exponents of its two position characters
`realInducedFirstCharacter` and `realInducedSecondCharacter`. -/
def realBlockSupport : RealBlock → List ℂ
  | .character d => [d.exponent]
  | .induced d => [d.exponent + (d.weight.natAbs : ℂ) / 2, d.exponent - (d.weight.natAbs : ℂ) / 2]

/-- The exponent support of a list of real blocks: the exponents at all diagonal positions,
block by block. Up to order it is the infinitesimal character of the standard module, as an
element of `ℂ^N` modulo permutations. -/
def realExponentSupport (ds : List RealBlock) : List ℂ :=
  ds.flatMap realBlockSupport

/-- The squared weight of a real block: `0` for a character and `m^2` for the real induction
of `(z/|z|)^m |z|^(2t)`. -/
def realBlockWeightSquare : RealBlock → ℕ
  | .character _ => 0
  | .induced d => d.weight.natAbs ^ 2

/-- The sum of the squared weights of a list of real blocks. -/
def realWeightSquareSum (ds : List RealBlock) : ℕ :=
  (ds.map realBlockWeightSquare).sum

/-! ## The rank-one step -/

/-- The rank-one step of the Langlands classification of `GL_n(ℝ)`, in quotient form. Let
`(ρ, π)` be an irreducible admissible `(𝔤𝔩_n(ℝ), O(n))`-module and let `pre ++ x :: y :: post`
be a list of real blocks of total rank `n` in which the adjacent blocks `x, y` are in the
wrong order: `Re t(x) < Re t(y)`. If `(ρ, π)` receives a nonzero intertwiner from the
`O(n)`-finite functions of the standard module of `pre ++ x :: y :: post`, then either

* it receives a nonzero intertwiner from the standard module of `pre ++ y :: x :: post`
  (the two blocks exchanged), or
* there is a list `zs` of real blocks whose exponent support is a permutation of that of
  `[x, y]` and whose sum of squared weights is strictly larger than that of `[x, y]`, such
  that `(ρ, π)` receives a nonzero intertwiner from the standard module of
  `pre ++ zs ++ post`. -/
def RealRankOneStepStatement : Prop :=
  ∀ (n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V)
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V)
    (pre post : List RealBlock) (x y : RealBlock)
    (B : kFiniteFunctions (realStandardModule n (pre ++ x :: y :: post))
      (unitaryCompact ℝ n) →ₗ[ℂ] V),
    IsRealGKModule n ρ π → IsIrreducibleGKModule ρ π → IsAdmissibleGKModule ρ →
      realRank (pre ++ x :: y :: post) = n →
      realBlockExponent x < realBlockExponent y →
      B ≠ 0 → IsRealStandardIntertwiner n ρ π (pre ++ x :: y :: post) B →
        (∃ B' : kFiniteFunctions (realStandardModule n (pre ++ y :: x :: post))
            (unitaryCompact ℝ n) →ₗ[ℂ] V,
          B' ≠ 0 ∧ IsRealStandardIntertwiner n ρ π (pre ++ y :: x :: post) B') ∨
        ∃ zs : List RealBlock,
          (realExponentSupport zs).Perm (realExponentSupport [x, y]) ∧
          realWeightSquareSum [x, y] < realWeightSquareSum zs ∧
          ∃ B' : kFiniteFunctions (realStandardModule n (pre ++ zs ++ post))
              (unitaryCompact ℝ n) →ₗ[ℂ] V,
            B' ≠ 0 ∧ IsRealStandardIntertwiner n ρ π (pre ++ zs ++ post) B'

/-- The rank-one step implies the Langlands classification starting from a principal-series
quotient. -/
def RealLanglandsFromRankOneStepReductionStatement : Prop :=
  RealRankOneStepStatement.{uV} → RealLanglandsFromPrincipalSeriesStatement.{uV}

/-! ## Combinatorics of the exponent support and the weights -/

theorem length_realBlockSupport (d : RealBlock) : (realBlockSupport d).length = d.rank := by
  cases d <;> rfl

/-- The exponent support has one entry per diagonal position. -/
theorem length_realExponentSupport (ds : List RealBlock) :
    (realExponentSupport ds).length = realRank ds := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
      rw [realRank_cons, ← ih, ← length_realBlockSupport]
      simp [realExponentSupport]

theorem realExponentSupport_append (ds es : List RealBlock) :
    realExponentSupport (ds ++ es) = realExponentSupport ds ++ realExponentSupport es := by
  simp [realExponentSupport]

theorem realWeightSquareSum_append (ds es : List RealBlock) :
    realWeightSquareSum (ds ++ es) = realWeightSquareSum ds + realWeightSquareSum es := by
  simp [realWeightSquareSum]

/-- Exchanging two adjacent blocks permutes the exponent support. -/
theorem realExponentSupport_swap (pre post : List RealBlock) (x y : RealBlock) :
    (realExponentSupport (pre ++ y :: x :: post)).Perm
      (realExponentSupport (pre ++ x :: y :: post)) :=
  ((List.Perm.swap x y post).append_left pre).flatMap_right realBlockSupport

/-- Exchanging two adjacent blocks keeps the sum of squared weights. -/
theorem realWeightSquareSum_swap (pre post : List RealBlock) (x y : RealBlock) :
    realWeightSquareSum (pre ++ y :: x :: post) = realWeightSquareSum (pre ++ x :: y :: post) :=
  (((List.Perm.swap x y post).append_left pre).map realBlockWeightSquare).sum_eq

/-- The sum of squared weights is bounded by twice the sum of the squared real parts of the
exponent support: a real induction of weight `m` and exponent `t` contributes `m^2` on the
left and `2((Re t + |m|/2)^2 + (Re t - |m|/2)^2) = 4 (Re t)^2 + m^2` on the right. -/
theorem realWeightSquareSum_le (ds : List RealBlock) :
    (realWeightSquareSum ds : ℝ) ≤
      2 * ((realExponentSupport ds).map fun s => s.re ^ 2).sum := by
  induction ds with
  | nil => simp [realWeightSquareSum, realExponentSupport]
  | cons d ds ih =>
      have hd : (realBlockWeightSquare d : ℝ) ≤
          2 * ((realBlockSupport d).map fun s => s.re ^ 2).sum := by
        cases d with
        | character c =>
            simp only [realBlockWeightSquare, realBlockSupport, List.map_cons, List.map_nil,
              List.sum_cons, List.sum_nil, Nat.cast_zero]
            positivity
        | induced c =>
            simp only [realBlockWeightSquare, realBlockSupport, List.map_cons, List.map_nil,
              List.sum_cons, List.sum_nil, Nat.cast_pow, Complex.add_re, Complex.sub_re,
              Complex.div_ofNat_re, Complex.natCast_re]
            nlinarith [sq_nonneg c.exponent.re]
      have hcons : realWeightSquareSum (d :: ds) =
          realBlockWeightSquare d + realWeightSquareSum ds := by
        simp [realWeightSquareSum]
      have hsupp : realExponentSupport (d :: ds) = realBlockSupport d ++ realExponentSupport ds :=
        by simp [realExponentSupport]
      rw [hcons, hsupp, List.map_append, List.sum_append, Nat.cast_add]
      linarith

/-! ## Inversions -/

/-- The number of inversions of a list of real blocks: pairs of blocks, the first before the
second, whose real exponents are strictly increasing. -/
def realInversionCount : List RealBlock → ℕ
  | [] => 0
  | a :: l =>
      l.countP (fun b => decide (realBlockExponent a < realBlockExponent b)) +
        realInversionCount l

/-- Exchanging an adjacent strictly increasing pair removes an inversion. -/
theorem realInversionCount_swap_lt (pre post : List RealBlock) {x y : RealBlock}
    (hxy : realBlockExponent x < realBlockExponent y) :
    realInversionCount (pre ++ y :: x :: post) < realInversionCount (pre ++ x :: y :: post) := by
  induction pre with
  | nil =>
      have hyx : ¬ realBlockExponent y < realBlockExponent x := not_lt.2 hxy.le
      simp only [List.nil_append, realInversionCount, List.countP_cons, hxy, hyx,
        decide_true, decide_false, Bool.false_eq_true, ↓reduceIte]
      omega
  | cons a pre ih =>
      simp only [List.cons_append, realInversionCount]
      rw [((List.Perm.swap x y post).append_left pre).countP_eq]
      omega

/-- A list of real blocks not in Langlands order has an adjacent strictly increasing pair. -/
theorem exists_adjacent_inversion_of_not_ordered :
    ∀ {ds : List RealBlock}, ¬ IsRealLanglandsOrdered ds →
      ∃ (pre : List RealBlock) (x y : RealBlock) (post : List RealBlock),
        ds = pre ++ x :: y :: post ∧ realBlockExponent x < realBlockExponent y
  | [], h => absurd List.Pairwise.nil h
  | [a], h => absurd (List.pairwise_singleton _ a) h
  | a :: c :: l, h => by
      by_cases hl : IsRealLanglandsOrdered (c :: l)
      · by_cases hac : realBlockExponent a < realBlockExponent c
        · exact ⟨[], a, c, l, rfl, hac⟩
        · exfalso
          apply h
          unfold IsRealLanglandsOrdered at hl ⊢
          refine List.Pairwise.cons ?_ hl
          intro b hb
          have hca : realBlockExponent c ≤ realBlockExponent a := not_lt.1 hac
          rcases List.mem_cons.1 hb with rfl | hb
          · exact hca
          · exact le_trans (List.rel_of_pairwise_cons hl hb) hca
      · obtain ⟨pre, x, y, post, hds, hxy⟩ := exists_adjacent_inversion_of_not_ordered hl
        exact ⟨a :: pre, x, y, post, by rw [hds, List.cons_append], hxy⟩

/-! ## The reduction -/

/-- The reduction: starting from the principal series, apply the rank-one step at an adjacent
inversion as long as the list of blocks is not in Langlands order. The exponent support stays
a permutation of that of the principal series, so the total rank stays `n` and the sum of
squared weights stays below `K = ⌊2 Σ (Re s)^2⌋`; the pair (`K` minus the sum of squared
weights, number of inversions) decreases lexicographically at every step. -/
theorem realLanglandsFromPrincipalSeries_of_rankOneStep :
    RealLanglandsFromRankOneStepReductionStatement.{uV} := by
  intro hA n V _ _ ρ π cs B hgk hirr hadm hlen hB0 hBint
  set S₀ := realExponentSupport (cs.map RealBlock.character) with hS₀
  have hS₀len : S₀.length = n := by
    rw [hS₀, length_realExponentSupport, realRank_map_character, hlen]
  set K : ℕ := ⌊2 * (S₀.map fun s => s.re ^ 2).sum⌋₊ with hK
  have hWK : ∀ ds : List RealBlock, (realExponentSupport ds).Perm S₀ →
      realWeightSquareSum ds ≤ K := by
    intro ds hds
    apply Nat.le_floor
    have h := realWeightSquareSum_le ds
    rwa [(hds.map fun s : ℂ => s.re ^ 2).sum_eq] at h
  have hrank : ∀ ds : List RealBlock, (realExponentSupport ds).Perm S₀ → realRank ds = n := by
    intro ds hds
    rw [← length_realExponentSupport, hds.length_eq, hS₀len]
  suffices h : ∀ a b : ℕ, ∀ ds : List RealBlock, K - realWeightSquareSum ds = a →
      realInversionCount ds = b → (realExponentSupport ds).Perm S₀ →
      (∃ B' : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n) →ₗ[ℂ] V,
          B' ≠ 0 ∧ IsRealStandardIntertwiner n ρ π ds B') →
      ∃ ds : List RealBlock, realRank ds = n ∧ IsRealLanglandsOrdered ds ∧
          ∃ B' : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n) →ₗ[ℂ] V,
            B' ≠ 0 ∧ IsRealStandardIntertwiner n ρ π ds B' from
    h _ _ _ rfl rfl (List.Perm.refl _) ⟨B, hB0, hBint⟩
  intro a
  refine Nat.strong_induction_on a ?_
  intro a iha b
  refine Nat.strong_induction_on b ?_
  intro b ihb ds ha hb hsupp hB₁
  obtain ⟨B₁, hB₁0, hB₁⟩ := hB₁
  by_cases hord : IsRealLanglandsOrdered ds
  · exact ⟨ds, hrank ds hsupp, hord, B₁, hB₁0, hB₁⟩
  obtain ⟨pre, x, y, post, rfl, hxy⟩ := exists_adjacent_inversion_of_not_ordered hord
  rcases hA n V ρ π pre post x y B₁ hgk hirr hadm (hrank _ hsupp) hxy hB₁0 hB₁ with
    ⟨B₂, hB₂0, hB₂⟩ | ⟨zs, hzs, hW, B₂, hB₂0, hB₂⟩
  · -- The two blocks are exchanged: the weights stay, one inversion disappears.
    have hsupp' := (realExponentSupport_swap pre post x y).trans hsupp
    have hinv := realInversionCount_swap_lt pre post hxy
    have hW' := realWeightSquareSum_swap pre post x y
    exact ihb _ (by omega) (pre ++ y :: x :: post) (by omega) rfl hsupp' ⟨B₂, hB₂0, hB₂⟩
  · -- The pair is replaced: the sum of squared weights grows and stays below `K`.
    have hpair : realExponentSupport (pre ++ x :: y :: post) =
        realExponentSupport pre ++ realExponentSupport [x, y] ++ realExponentSupport post := by
      rw [show pre ++ x :: y :: post = pre ++ [x, y] ++ post by simp,
        realExponentSupport_append, realExponentSupport_append]
    have hsupp' : (realExponentSupport (pre ++ zs ++ post)).Perm S₀ := by
      refine List.Perm.trans ?_ hsupp
      rw [hpair, realExponentSupport_append, realExponentSupport_append]
      exact (hzs.append_left _).append_right _
    have hle := hWK _ hsupp'
    have hlt : realWeightSquareSum (pre ++ x :: y :: post) <
        realWeightSquareSum (pre ++ zs ++ post) := by
      rw [show pre ++ x :: y :: post = pre ++ [x, y] ++ post by simp,
        realWeightSquareSum_append, realWeightSquareSum_append, realWeightSquareSum_append,
        realWeightSquareSum_append]
      omega
    exact iha _ (by omega) _ _ rfl rfl hsupp' ⟨B₂, hB₂0, hB₂⟩

end Langlands.Archimedean
