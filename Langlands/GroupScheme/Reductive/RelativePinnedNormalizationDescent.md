# Descent criterion for unique normalized comparisons

Worker 561.

This internal reduction combines actual comparison descent with fppf
reflection of inner equivalence. It supplies a sufficient criterion for
`AffinePinnedModel.HasUniqueNormalizedComparisons P`; it constructs neither
the predicate `P` nor its local normalized representatives.

`innerEquivalent_of_pullComparison` reflects inner equivalence along an
arbitrary flat, surjective, locally finitely presented cover of the common
scheme. To use the reflection theorem for ordinary base change, the proof
conjugates both direct comparisons by the actual `baseChangeCompIso`
identifications, giving `comparisonToIterated`. The inverse and forward
statements give `innerEquivalent_pullComparison_iff`.

`IsFppfLocalComparisonPredicate P` requires that `P` be preserved by arbitrary
`pullComparison` and reflected by an fppf cover.
`HasFppfLocalNormalizedComparisons P` requires that each given comparison,
after some fppf cover, have a normalized representative of its local-inner
class, unique among normalized representatives of that class. It also
explicitly requires independence of the representative's all-test
`comparisonLocalIso` family. This independence is a retained geometric
obligation; uniqueness is not used to infer it implicitly.

The theorem `hasUniqueNormalizedComparisons_of_fppf` glues the independent
local comparison using `descendComparison`. Its exact pullback recovery,
the locality of `P`, and reflection of inner equivalence show that the
glued comparison has the required two properties. Any competing global
normalized representative pulls back to a local competitor, so local
uniqueness and `pullComparison_injective` give global uniqueness.

All schemes and all test schemes are arbitrary in the same universe.
There is no affineness, connectedness, nonemptiness or constant
root-datum-label hypothesis. Constructing the local normalized
representatives, proving their independence and local uniqueness, and
establishing the predicate's geometric and coherence properties remain
necessary to apply this criterion to the pinned comparison target.
