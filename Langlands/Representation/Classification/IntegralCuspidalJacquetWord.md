# Actual integral cuspidal Jacquet words

`Langlands.Classification.IntegralCuspidalJacquetWord F T m n A π w`
is a predicate on finite integer lists. The field is an arbitrary finite
p-adic extension with supplied topological data `T`. The actual
supercuspidal object `A` has rank `m`, and the actual smooth complex object
`π` has rank `n`. Their carriers lie in `Type (max uF uV)`, with independent
field and carrier universe parameters.

The predicate means that there exist a positive block shape `B` of total
rank `n`, actual supercuspidal objects `C i` on its blocks, and integer
exponents `e i` such that all of the following hold:

- The list `w` is exactly `List.ofFn e`, in block order.
- For each block, the rank-indexed supercuspidal class of `C i` is the
  rank-indexed class of `A` twisted by `|det|^(e i)`. Equality takes place
  in the dependent sum over ranks. It therefore includes the equality
  `B.size i = m` and the necessary transport of classes.
- The actual external smooth tensor of the objects `C i` is an actual
  `SmoothRep.IsSubquotient` of `(T.normalizedJacquetFunctor B).obj π`.

The twist and Jacquet functor use the supplied `T`, its residue-normalized
absolute value, and the existing normalized upper parabolic conventions.
The tensor and the subquotient relation are the existing actual constructions.
No Grothendieck-group equality replaces the occurrence condition.

This is an internal interface for applying finite integer-word arguments to
actual Jacquet subquotients. It is assembled from existing definitions,
rather than transcribing a new assertion from the literature. The definition
imposes no irreducibility, admissibility, finite length, unitarity or
square-integrability on `π`, and no unitarity on `A`. Those conditions can
be hypotheses of later existence or transfer theorems.

The definition allows rank zero and the empty block shape. For a nonempty
realization the positive block sizes force `m > 0`; no positivity assertion
is proved in this module. It asserts neither the existence of a realized
word nor closure under any permutation or local move. Selection of a least
word, transfer of actual subquotients, segment extraction, strong segment
heads and the analytic classification remain separate obligations.
