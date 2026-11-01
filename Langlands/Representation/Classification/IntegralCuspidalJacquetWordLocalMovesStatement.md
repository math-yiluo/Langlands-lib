# Conditional local moves for actual integral cuspidal Jacquet words

`Langlands.Classification.IntegralCuspidalJacquetWordLocalMoves` is a
proposition definition. It states a conditional consequence of three
separately defined representation-theoretic propositions:

- `AdjacentCuspidalJacquetInterchange.{uF,uV} F T`;
- `TwoSupercuspidalNonadjacentProductIrreducible.{uF,max uF uV} F T`;
- `RepeatedCuspidalTripleJacquetTransfer.{uF,uV} F T`.

All three are premises. Their proposition definitions do not establish
their truth.

For arbitrary ranks `m,n`, an actual supercuspidal representation `A` of
rank `m`, and an actual irreducible, admissible smooth representation `π`
of rank `n` with composition finite length, let
`P w := IntegralCuspidalJacquetWord F T m n A π w`.
For every integer prefix `l`, suffix `r` and indicated integer entries,
the conclusion consists of these three closure implications:

- If `a + 1 ≠ b` and `b + 1 ≠ a`, realization of
  `l ++ [a,b] ++ r` implies realization of `l ++ [b,a] ++ r`.
- Realization of `l ++ [b+1,b,b] ++ r` implies realization of
  `l ++ [b,b+1,b] ++ r`.
- Realization of `l ++ [b+1,b,b+1] ++ r` implies realization of
  `l ++ [b+1,b+1,b] ++ r` or `l ++ [b,b+1,b+1] ++ r`.

The last conclusion retains the disjunction. It does not select a branch
that works for every realization. Equal entries are permitted in the
first move; only differences of one are excluded. The prefix and suffix
remain unchanged in each conclusion.

The field prime, field `F` and supplied topological data `T` are arbitrary.
The field and carrier universe parameters are independent, with actual
carriers in `Type (max uF uV)`. The nonadjacent irreducibility proposition
is instantiated at this saturated carrier universe. No unitarity
assumption is imposed on `A`, and no analytic hypothesis is imposed on `π`.
All occurrences use the existing actual normalized upper Jacquet
subquotient predicate, not an equality of Grothendieck classes.

This is a derived interface connecting the existing occurrence predicate
and the existing actual-transfer statements to the three abstract
closures in `LexMinimalConsecutiveRuns`. An intended proof extracts the
realizing block shape and factors, translates integer differences and
repeats into their rank-indexed class relations, and applies the supplied
actual transfers. For the first move, positive block ranks and integral
twist freeness convert the excluded integer differences into excluded
one-step class relations. The supplied nonadjacent irreducibility and
the published irreducible equal-rank commutation theorem provide the
binary-product hypotheses of adjacent interchange. Reindexing the
actual factors then identifies each output word.

This statement neither proves any of its three representation-theoretic
premises nor supplies an initial realized word, a minimum, a segment
embedding, a strong segment head or the analytic classification.
