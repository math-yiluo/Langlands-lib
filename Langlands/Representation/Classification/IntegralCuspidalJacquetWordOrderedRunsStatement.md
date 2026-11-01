# A least realized word and its ordered consecutive runs

`IntegralCuspidalJacquetWordOrderedRuns F T` is a proposition definition
with arbitrary supplied p-adic field and topology, independent field and
carrier universes, and actual carriers in `Type (max uF uV)`.

Its explicit premises are the actual adjacent Jacquet interchange,
nonadjacent two-supercuspidal product irreducibility, and repeated-factor
triple transfer propositions. For every actual supercuspidal object `A`
and irreducible, admissible, composition-finite-length actual object `π`,
it takes an integer word `w₀` already realized by
`IntegralCuspidalJacquetWord F T m n A π`.

The conclusion supplies a word `w` realized by the same predicate, with
`w.Perm w₀`, which is lexicographically least among the realized
permutations of `w₀`. Thus the permutation relation retains all integer
entries and their multiplicities, and minimality compares only words in
this fixed permutation class. No minimum among all realized integer words
is asserted.

The same `w` is a concatenation of nonempty descending consecutive runs
`[a,a-1,...,a-(k-1)]`, specified by pairs `(a,k)` with `k > 0`.
The first coordinates of adjacent runs are weakly increasing, as expressed
by `List.IsChain`. The empty input word is allowed and can give an empty
list of runs. Neither uniqueness nor maximality of runs is asserted.

This is a derived interface combining finite permutation-class minimum
selection and the finite-word consecutive-run argument with conditional
local closure of actual Jacquet words. To apply the latter argument one
restricts its predicate to words that are both realized and permutations
of `w₀`. Each of its two-entry and three-entry moves preserves this
permutation relation, including either alternative of the upper-repeat
move. Hence minimum selection in a finite permutation class suffices;
one does not need a well-ordering of arbitrary integer words.

The statement retains actual external-tensor subquotient occurrence
through the unchanged word predicate. It constructs no initial word,
proves none of the three supplied representation-theoretic propositions,
and assumes rather than derives admissibility and finite length. Its
conclusion is an integer-word decomposition, with no segment subrepresentation,
segment head, extremal multiplicity, Casselman inequality, unitarity or
analytic classification assertion. Passing from these runs to any such
representation-theoretic conclusion remains a separate obligation.
