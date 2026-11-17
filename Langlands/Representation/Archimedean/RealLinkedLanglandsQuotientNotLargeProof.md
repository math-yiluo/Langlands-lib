# Linked Langlands quotients are not maximally faithful: proof of `RealLinkedLanglandsQuotientNotLargeStatement`

Lean module: `Langlands.Representation.Archimedean.RealLinkedLanglandsQuotientNotLargeProof`,
namespace `Langlands.Archimedean`.

This module proves the Library statement `RealLinkedLanglandsQuotientNotLargeStatement` (module
`RealLargeStandardIrreducibleReduction`) as the theorem
`Langlands.Archimedean.realLinkedLanglandsQuotientNotLarge`. The proof only assembles theorems that
are already proved in the Library. It adds no new mathematics, and each of the three theorems
below is a single term built from Library theorems.

## The statement

Let `ds` be a list of real blocks of total rank `n` (`realRank ds = n`) in Langlands order
(`IsRealLanglandsOrdered ds`), and suppose that two of its Mœglin data are linked
(`¬ IsRealMoeglinUnlinked ds`). Let `R` be a proper `(𝔤, K)`-submodule of the `O(n)`-finite
functions of `realStandardModule n ds` that contains every proper `(𝔤, K)`-submodule. Then the
quotient by `R`, the Langlands quotient, is not maximally faithful:
`¬ IsMaximallyFaithfulModulo (realStandardLie n ds) R`. The theorem keeps every quantifier and
hypothesis of the statement.

## The proof

### 1. Unlinked swaps: `realUnlinkedSwap : RealUnlinkedSwapStatement`

`RealUnlinkedSwapStatement` (module `RealStandardIrreducibleCriterionReduction`) says: for lists
`pre`, `post` and real blocks `x`, `y` of total rank `n` with `Re t(y) ≤ Re t(x)` whose Mœglin
data are not linked, there is an injective `(𝔤, K)`-intertwiner from the `O(n)`-finite functions
of the standard module of `pre ++ x :: y :: post` to those of `pre ++ y :: x :: post`.

The Library theorem `realUnlinkedSwapReduction : RealUnlinkedSwapReductionStatement` (module
`RealUnlinkedSwapReduction`) derives it from four statements, one for each kind of pair of
adjacent blocks. All four are proved Library theorems, and the proof applies the reduction to
them:

* two characters: `RealCharacterSwap.realCharacterSwap : RealCharacterSwapStatement` (module
  `RealCharacterSwapProof`);
* a character, then an induction block of nonzero weight:
  `realCharacterInducedSwap : RealCharacterInducedSwapStatement` (module
  `RealCharacterInducedUnlinked`);
* an induction block of nonzero weight, then a character:
  `realInducedCharacterSwap : RealInducedCharacterSwapStatement` (module
  `RealInducedCharacterUnlinked`);
* two induction blocks of nonzero weights: `realInducedSwap : RealInducedSwapStatement` (module
  `RealInducedSwapUnlinked`).

### 2. The Jacquet functional: `realLinkedJacquetFunctional : RealLinkedJacquetFunctionalStatement`

`RealLinkedJacquetFunctionalStatement` (module `RealLinkedJacquetFunctional`) says: for `ds` as in
the target (rank `n`, Langlands order, a linked pair), the `O(n)`-finite functions of the standard
module carry a nonzero real Jacquet functional `ℓ` with exponents `a` and signs `e`, together with
a position `p` (`p + 1 < n`) and `k : ℕ` such that `a_p - a_{p+1} = 1 - k` and `ℓ` kills
`π(E_{p+1,p})^k v` for every `v`.

The Library theorem `realLinkedJacquetFunctionalReduction` (module
`RealLinkedJacquetPairReduction`) derives it from four statements. The proof applies the
reduction to four proved theorems:

1. induction in stages: `realLinkedJacquetFunctionalInStages :
   RealLinkedJacquetFunctionalInStagesStatement` (module `RealLinkedJacquetInStagesProof`);
2. unlinked swaps: `realUnlinkedSwap` from step 1;
3. injective swap intertwiners are surjective: `realSwapInjectiveIntertwinerSurjective :
   RealSwapInjectiveIntertwinerSurjectiveStatement` (module `RealSwapSurjectiveProof`);
4. two linked blocks: `realPairLinkedJacquetFunctional :
   RealPairLinkedJacquetFunctionalStatement` (module `RealPairLinkedJacquetFunctionalProof`).

The reduction's conclusion is `RealLinkedJacquetFunctionalExists n ds` under the same hypotheses.
Lean accepts it as `RealLinkedJacquetFunctionalStatement` without any rewriting.

### 3. The target: `realLinkedLanglandsQuotientNotLarge`

Two Library theorems finish the proof.

* `realLinkedQuotientGrowth_of_split` (module `RealLinkedJacquetFunctional`) proves
  `RealLinkedQuotientGrowthStatement` from three statements, which the proof supplies:
  * S1, `realLeftPolynomialGrowth : RealLeftPolynomialGrowthStatement` (module
    `RealLeftPolynomialGrowthProof`);
  * S3, `realTaylorLeftPolynomial : RealTaylorLeftPolynomialStatement` (module
    `RealTaylorLeftPolynomialProof`);
  * S2, `realLinkedJacquetFunctional` from step 2.

  `RealLinkedQuotientGrowthStatement` says: for `ds` as in the target there is a proper
  `(𝔤, K)`-submodule `W` and a constant `C` such that, for every `d`, the operators
  `v ↦ u v mod W` with `u` of degree at most `d` in `U(ℂ ⊗_ℝ 𝔤𝔩_n(ℝ))` span a space of dimension
  at most `C (d + 1)^(n (n - 1) - 1)`.
* `realLinkedLanglandsQuotientNotLarge_of_quotientGrowth` (module `RealStandardCentralGrowth`)
  turns this upper bound into the target. It compares the bound with the Library's lower bound
  `realStandardCentralGrowth`: a linear map on `U(ℂ ⊗_ℝ 𝔤𝔩_n(ℝ))` that kills an element of
  degree at most `d` only when that element lies in the central ideal `realStandardCentralIdeal n
  ds` has an image of the degree-`≤ d` part of dimension at least `c (d + 1)^(n (n - 1))`, for some
  `c > 0`. If the Langlands quotient were maximally faithful, then `u ↦ (v ↦ u v mod W)` would be
  such a map, because `W ⊆ R`. The two bounds contradict each other for large `d`.

## Axioms

`realLinkedLanglandsQuotientNotLarge` depends only on the standard axioms `propext`,
`Classical.choice` and `Quot.sound`.
