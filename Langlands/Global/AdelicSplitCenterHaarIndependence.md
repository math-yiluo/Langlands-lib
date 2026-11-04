# Independence of splitting coordinates in normalized adelic Haar measures

Author: Worker 112.

This is an internal consequence of `AdelicNormOneDecomposition`,
`AdelicSplitCenterHaar` and `AdelicSplitCenterSubgroupHaar`, using Mathlib's
injectivity of measure pushforward along a measurable embedding, product
measure on rectangles, and local finiteness and open positivity of Haar
measure. It adds no external existence assertion.

Let `F : Type u` be a number field, `G/F` an actual affine locally finite
type group scheme, `T/F` an actual commutative group scheme, and
`i : T.toGrp ⟶ G` an actual homomorphism. Retain injectivity of
`characterRestrict i`, finite index of its range, scheme-theoretic centrality
`hc : IsCentral i`, and a supplied finite splitting `e` of `T`. All point
groups and their measurable structures remain the existing ones.

`normalizedPositiveHaarMeasure_unique` considers any measure `μ` on
`intrinsicSubgroup F T`. If the pushforward of `μ` times the existing Haar
measure on `normOneSubgroup F G` through actual multiplication is exactly
the existing ambient Haar measure, then `μ` equals
`normalizedPositiveHaarMeasure F G T i hi I e hc`. No Haar, regularity or
sigma-finiteness assumption is imposed on this arbitrary `μ`.

To prove this, compare its pushforward with the already proved normalized
product identity. The multiplication homeomorphism is a measurable
equivalence, so its pushforward is injective and the two product measures
are equal. Local finiteness of norm-one Haar gives an open neighborhood of
the identity of finite measure. Open positivity makes this measure strictly
positive. Evaluate equality of the products on a rectangle formed from any
measurable positive-factor set and this neighborhood. The product formula
gives equality after multiplication by the same finite nonzero extended
nonnegative real number. Cancellation gives equality on the original
measurable set, hence equality of measures.

For any other finite index type `J : Type u` and supplied splitting `e'`
of the same `T`,
`normalizedPositiveHaarMeasure_eq_of_splitting` proves literal equality of
the two normalized positive measures. Both multiplication maps are the same
function `(a,n) ↦ positivePointMap a * n`; the splitting coordinates occur
only in the inverse and its proofs. Apply the uniqueness theorem using the
normalized product identity for the second splitting.

`positiveRationalSubgroupHaarMeasure_eq_of_splitting` gives literal equality
of the full Haar measures on the existing
`positiveRationalSubgroup F G T i`. Each measure is the pushforward of the
corresponding normalized positive measure times the same principal counting
measure through `(a,q) ↦ positivePointMap a * q.val.val`. Equality of the
positive measures and equality of these forward functions prove the claim.

These comparisons give constructions requiring only the split-torus
property `hT : IsSplitTorus T.toGrp`, in place of a supplied coordinate
presentation. `intrinsicPositiveHaarMeasure` chooses a finite splitting
witness from `hT`, equips its finite index type with a `Fintype` instance,
and applies the existing normalized measure construction.
`intrinsicPositiveHaarMeasure_eq` proves that the result agrees with that
construction for every supplied finite splitting. Its Haar theorem reuses
the existing normalized positive Haar theorem.
`measurePreserving_normOneDecomposition_intrinsic` rewrites by this
equality to prove that actual multiplication with any supplied splitting
preserves intrinsic positive Haar times the fixed norm-one Haar and the
fixed ambient Haar.

`intrinsicPositiveRationalSubgroupHaarMeasure` similarly chooses a finite
splitting witness and applies the existing full subgroup Haar construction.
Its `_eq` theorem identifies it with the construction for every supplied
splitting, and its `_isHaarMeasure` theorem transfers the existing Haar
property. These definitions therefore supply measures with no splitting
coordinates among their arguments, together with exact comparison laws;
the implementation uses classical choice and the proved independence.

The finite index types may be empty, so rank zero is included. The theorem
holds the actual torus `T`, its map `i`, and the ambient and norm-one Haar
choices fixed. It does not assert that the initial unnormalized
`positiveHaarMeasure` is independent of coordinates, or compare Haar choices
on different ambient or norm-one groups. Comparison between different
actual tori, identification with Getz--Hahn's greatest rational split
centre, general reductive torus existence, unimodularity, reduction and
finite volume remain separate obligations.
