# Ordered runs of a least realized cuspidal Jacquet word

`integralCuspidalJacquetWordOrderedRuns` proves
`IntegralCuspidalJacquetWordOrderedRuns` with the statement's three explicit
actual transfer and irreducibility premises. It also retains the supplied
initial realization and the irreducibility, admissibility and composition
finite length of `π`.

Write `P` for the actual integral cuspidal Jacquet word predicate with
`F,T,m,n,A,π` fixed. `Combinatorics.permutationLexMinimum` selects a word
`w` with `P w` and `w.Perm w₀` that has no strictly smaller realized
competitor in this permutation class. The finite selection theorem uses
the supplied realization of `w₀`.

The proof obtains the three local closures of `P` from
`integralCuspidalJacquetWordLocalMoves` and the supplied actual propositions.
It defines `Q v` to mean `P v ∧ v.Perm w₀`. Four short list lemmas prove
that the adjacent swap, lower-repeat move and either upper-repeat move
give a permutation of the original word, inside the same outside prefix
and suffix. Each lemma uses `List.Perm.swap`, with an additional fixed
head for the upper-left alternative, and then appends the outside lists.
Composing that permutation with the input's relation to `w₀` proves
closure of `Q`. The upper-repeat case retains the supplied alternative
and establishes membership in the permutation class in each branch.

Minimum selection now gives global lexicographic minimality for `Q`,
because membership in `Q` already includes the permutation-class
restriction. Applying `Combinatorics.lexMinimalConsecutiveRuns` to `Q`
gives the required positive-length runs, their weakly increasing initial
entries, and their exact concatenation to the same realized word `w`.
The result assembles these runs with the original realization,
permutation relation and restricted minimality.

This is an internal composition of the named finite-word and conditional
actual-word results. The explicit actual propositions, ambient finiteness
conditions and initial realization are not discharged here. No extraction
of segment representations or strong-head assertion follows just from
the integer-word decomposition.
