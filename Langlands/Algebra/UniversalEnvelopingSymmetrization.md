# Symmetrization into the genuine universal enveloping algebra

This internal construction uses the actual Mathlib universal enveloping algebra
and the previously constructed filtration by powers of constants plus Lie
generators. It does not replace that algebra or assume a PBW isomorphism.

For any commutative ring and Lie algebra, `word` multiplies the canonical Lie
generators in a list, in their specified order, with the empty word equal to one.
`word_mem_degreeFiltration` places a word in the piece indexed by its length.
`word_sub_word_mem_of_perm` proves that two permutation-equivalent lists have
word difference in degree at most their common length minus one. The proof is
induction on list permutations. An adjacent swap contributes a degree-one
commutator times the tail word. A common initial factor uses multiplicativity;
the empty-tail case is handled explicitly. Transitivity adds the differences.
Thus the degree-zero case also holds, where both words are one.

For a field `R : Type` and a Lie algebra in any universe, `orderedWord d` is the
multilinear product on `Fin d` obtained by applying the canonical generators to
Mathlib's ordered multilinear algebra product. `symmetricWord d` averages its
permutations with coefficient the inverse of the cardinality of the permutation
group. That cardinality is `d!`. Reindexing the finite sum by left multiplication
proves permutation invariance. The construction `symmetrize d` therefore
descends through the actual symmetric tensor quotient using
`SymmetricTensors.lift`; its pure-tensor value is `symmetricWord d`.
Both the average and the image of every symmetric tensor lie in degree `d`.
The tensor image claim uses the pure-tensor spanning theorem.

The average and its naturality exist over any field; if the characteristic
divides the group cardinality, this inverse coefficient is zero.
`symmetricWord_sub_orderedWord_mem` assumes characteristic zero, ensuring that
the coefficient normalizes the sum. It rewrites average minus word as the same
coefficient times the sum of the permutation-word differences, placing the
result in degree `d - 1`. All natural degrees, including zero, are retained.

`map_word`, `map_orderedWord`, `map_symmetricWord` and `map_symmetrize` express
naturality under an algebra map compatible with a specified linear map on the
generators. The last identity uses the actual symmetric quotient map provided
by the companion `SymmetricPowerMaps` module and extends pure-tensor naturality
by spanning. Neither a Lie-map hypothesis on the specified linear map nor
injectivity is needed beyond the explicit compatibility with the algebra map.

This is derived algebraic infrastructure. It does not identify the direct sum
of symmetric powers with the symmetric algebra, prove injectivity or
surjectivity of symmetrization, transfer finite covariants to enveloping central
generation, or prove the host automorphic differential-growth statement.
