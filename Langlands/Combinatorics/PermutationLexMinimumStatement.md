# A least word among the realized permutations of one word

`Langlands.Combinatorics.PermutationLexMinimum` is a proposition definition.
It states that, for any predicate `P` on finite integer lists and any word
`w₀` satisfying `P`, there is a word `w` such that:

- `P w` holds.
- `w.Perm w₀`, so the entries and their multiplicities are unchanged.
- No word `v` satisfying both `P v` and `v.Perm w₀` is strictly
  lexicographically smaller than `w`.

The comparison is the ordinary strict `List.Lex (· < ·)` on integer lists.
The conclusion allows repeated entries, negative integers and the empty word.
It imposes no local closure hypothesis on `P` and asserts no minimality
outside the permutation class of `w₀`.

This is a derived elementary finite-order interface. Its intended derivation
is to filter the finite list of permutations of `w₀` by `P` and choose the
least element of the resulting nonempty finite set. This uses only finite
enumeration and the lexicographic linear order on integer lists; it is not
a transcription of a representation-theoretic assertion.

For an actual Jacquet-word predicate, an application must first provide a
realized word `w₀`. Local moves made in a later argument must preserve the
permutation class in order to use this restricted minimum. The proposition
does not assert that all realized Jacquet words form a finite set, that any
realized word exists, or that actual Jacquet subquotients satisfy any local
transfer. It supplies no segment extraction or analytic classification.
