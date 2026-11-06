# Pole orders at `s = 0` of essentially square-integrable pairs

This module computes the order of the pole at `s = 0` of `L(s, π × σ)` for two
irreducible essentially square-integrable representations `π` and `σ` that are
components of the inductions of centered segments of irreducible supercuspidal
representations `π₀` and `σ₀`, as in Theorem (8.2) of JPSS 1983. All results
are conditional. They take the Library's unproved statements of JPSS 1983,
Proposition (8.1) and Theorem (8.2), as explicit hypotheses:
`SupercuspidalUnequalRankLFactorStatement` ((8.1)(i)),
`SupercuspidalEqualRankLFactorStatement` ((8.1)(ii)) and
`SquareIntegrableLFactorStatement` ((8.2)), all in
`TemperedLFactorStatement`. The Whittaker type of the twisted supercuspidal
blocks is also an explicit hypothesis, because (8.1) asks for it and the
Library does not yet prove that irreducible supercuspidal representations are
of Whittaker type.

## Provenance

Derived. Jacquet, Piatetski-Shapiro and Shalika, *Rankin-Selberg convolutions*,
Amer. J. Math. 105 (1983), Theorem (8.2), printed pages 444-445, and
Proposition (8.1), printed page 443. Let `π` be a component of the induction of
`π₀ ⊗ α^(m/2), …, π₀ ⊗ α^(-m/2)` and `σ` one of the induction of
`σ₀ ⊗ α^(n/2), …, σ₀ ⊗ α^(-n/2)`, with `α = |det|`. If `t ≤ r` for the ranks
`r + 1` of `π` and `t + 1` of `σ`, then (8.2) gives
`L(s, π × σ) = ∏_(j=0)^n L(s, (π₀ ⊗ α^(m/2)) × (σ₀ ⊗ α^(n/2 - j)))`.
Each factor is the L-factor of a pair of supercuspidal representations,
computed by (8.1). If `π₀` and `σ₀` have different ranks, (8.1)(i) makes every
factor `1`. If they have the same rank, the module `SupercuspidalPairPoleOrder`
shows that (8.1)(ii) gives the factor for `j` a pole of order
`[π₀ ⊗ α^(m/2) ≃ (σ₀ ⊗ α^(n/2 - j))^∨]` at `s = 0`. Henniart 2002, §4.2,
uses these pole orders at `s = 0`. The module records these consequences of
(8.1) and (8.2) in the Library's terms. In both theorems for either rank order,
the case `t > r` applies the same results with the roles of `π` and `σ`
exchanged. This is the convention of the Library's
`IsPadicSymmetricLPolynomial`, which uses the pair `(σ, π)` when `σ` has the
larger rank.

## Contents

- `isSupercuspidal_realPowerTwist_iff`: the twist `ρ ⊗ |det|^s` by a real
  power is supercuspidal exactly when `ρ` is. It specializes the Library's
  `isSupercuspidal_twist_iff` to the character
  `determinantPowerCharacter n s`.
- `isIrreducible_centeredSegmentBlocks` and
  `isSupercuspidal_centeredSegmentBlocks`: every block
  `centeredSegmentBlocks F m π₀ i = π₀ ⊗ α^(m/2 - i)` of the centered segment
  of an irreducible (respectively supercuspidal) `π₀` is irreducible
  (respectively supercuspidal). They use `isIrreducible_twist_iff` and the
  previous lemma.
- `centeredSegmentPoleCount F m n π₀ σ₀`: for `π₀` and `σ₀` representations of
  the same group `GL_(a+1)(F)`, the natural number
  `∑_(j=0)^n [π₀ ⊗ α^(m/2) ≃ (σ₀ ⊗ α^(n/2 - j))^∨]`. In Lean the term `j` is
  `contragredientIndicator F (centeredSegmentBlocks F m π₀ 0)
  (centeredSegmentBlocks F n σ₀ j)`. This is an internal definition: it names
  the sum of the pole orders of the factors in (8.2).
- `lPolynomialPoleOrderAtZero_one`: the polynomial `1` has pole order `0`.
- `lPolynomialPoleOrderAtZero_of_squareIntegrable_equalRank`: assume (8.2) and
  (8.1)(ii). Let `π₀` and `σ₀` be irreducible supercuspidal representations of
  `GL_(a+1)(F)`. Let `π` and `σ` be essentially square-integrable irreducible
  components (`IsIrreducibleComponent`) of the normalized inductions of
  `centeredSegmentBlocks F m π₀` and `centeredSegmentBlocks F n σ₀`. Their
  ranks are `r + 1 = (m + 1)(a + 1)` and `t + 1 = (n + 1)(a + 1)`, and
  `t ≤ r`. Assume every block of `σ₀`'s segment is of Whittaker type for
  `standardCharacter ψ a`. Then every `P` with
  `IsPadicPairLPolynomial F ψ ν.val π σ P` has
  `lPolynomialPoleOrderAtZero P = centeredSegmentPoleCount F m n π₀ σ₀`.
  The proof takes the factorization `P' = ∏_j Q_j` from (8.2) and identifies
  `P` with `P'` (`IsPadicPairLPolynomial.unique`). The pole order of the
  product is the sum of the pole orders of the factors
  (`lPolynomialPoleOrderAtZero_prod`). This additivity needs nonzero factors:
  each `Q_j` has constant coefficient `1`
  (`IsPadicSymmetricLPolynomial.coeff_zero`). Each `Q_j` is the L-polynomial
  of a pair of equal rank, so the symmetric relation is the plain one
  (`isPadicSymmetricLPolynomial_of_le`). Its pole order is the indicator by
  `lPolynomialPoleOrderAtZero_of_supercuspidalEqualRank`.
- `lPolynomialPoleOrderAtZero_of_squareIntegrable_ne_rank`: assume (8.2) and
  (8.1)(i) in both universe orders. In the same situation, except that `π₀` is
  a representation of `GL_(a+1)(F)` and `σ₀` one of `GL_(b+1)(F)` with
  `a ≠ b`, every such `P` has pole order `0`. Here the first block of `π₀`'s
  segment and every block of `σ₀`'s segment are assumed of Whittaker type. By
  (8.1)(i), each factor `Q_j` is `1`. If `b < a`, (8.1)(i) applies to the pair
  `(π₀ ⊗ α^(m/2), σ₀ ⊗ α^(n/2 - j))` directly. If `a < b`, it applies to the
  exchanged pair, which is the pair that `IsPadicSymmetricLPolynomial` uses
  (`isPadicSymmetricLPolynomial_of_lt`). Uniqueness of the L-polynomial then
  gives `Q_j = 1`, so `P = 1`, of pole order `0`.
- `le_iff_of_centeredSegment_rank`: if `(m + 1)(a + 1) = r + 1` and
  `(n + 1)(a + 1) = t + 1` (written as sums of constants, as in (8.2)), then
  `t ≤ r` exactly when `n ≤ m`.
- `lPolynomialPoleOrderAtZero_of_squareIntegrable_symmetric_equalRank`: the
  equal-rank result for the relation `IsPadicSymmetricLPolynomial`, without the
  hypothesis `t ≤ r`. It assumes (8.2) and (8.1)(ii) in both universe orders and
  the Whittaker type of every block of both segments. The pole order is
  `centeredSegmentPoleCount F m n π₀ σ₀` if `n ≤ m`, and
  `centeredSegmentPoleCount F n m σ₀ π₀` otherwise. The case `t ≤ r` is the
  equal-rank theorem. The case `r < t` is the equal-rank theorem for the
  exchanged pair `(σ, π)`.
- `lPolynomialPoleOrderAtZero_of_squareIntegrable_symmetric_ne_rank`: the
  different-rank result for `IsPadicSymmetricLPolynomial`, without the
  hypothesis `t ≤ r`, under the same symmetric hypotheses: the pole order is
  `0`. Both cases are the different-rank theorem, for `(π, σ)` and for
  `(σ, π)`.
