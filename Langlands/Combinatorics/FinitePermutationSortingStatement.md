# Finite sorting by adjacent strict inversions

Author: Worker 17.

This internal interface states a finite combinatorial lemma for the ordered
segment conversion. It has no literature attribution and makes no claim about
representations, segment linkage, induction, or analytic square-integrability.

`Langlands.Combinatorics.FinitePermutationSorting` quantifies over every natural
number `n`, real family `x : Fin n → ℝ`, and predicate `P` on permutations of
`Fin n`. A permutation maps each new position to its original label. The
hypotheses say that `P` holds for the identity and is preserved when positions
`j` and `j + 1` are swapped whenever the value at `j` is strictly smaller. The
composition is `swap.trans σ`, so the new family has value `x (σ (swap i))`.
The conclusion is one permutation satisfying both `P` and weak decrease of
its reordered real family. Every original label is retained exactly once,
including labels with repeated values. The statement also covers `n = 0`.

The use of an arbitrary invariant lets a consumer retain an isomorphism of
induced representations and a segment ordering condition while sorting. That
consumer must prove preservation under every strict adjacent inversion. This
interface does not supply those representation-theoretic facts. Equal values
do not require a swap. Stable relative order of equal labels is not asserted
by the conclusion unless included in the invariant.

The statement is motivated by minimizing the weighted sum
`∑ i, (i : ℝ) * x (σ i)` over the finite nonempty set of permutations satisfying
`P`. An adjacent strict inversion would decrease this sum, contradicting
minimality. This is an explanation of the proposed internal lemma, not an
implemented proof in this module. The Lean declaration is a `Prop`-valued
`def`; it introduces no axiom or theorem.
