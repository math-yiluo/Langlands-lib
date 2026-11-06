# A simple-coroot face for an actual split-torus centralizer

Authors: Worker 1577 and Worker 1352.

This internal construction starts with an actual
`SplitTorusCentralizerRootModel C` over a field, a split source torus `A`,
and the supplied all-test centralizer representative `j : M ⟶ G`.
Both `G` and `M` are affine and locally of finite type. The model provides
one actual split maximal torus `T` embedded in both groups and compatible
with `j`. Let `P` and `R` be supplied actual root data of the ambient and
centralizer embeddings, respectively, on the unchanged character and
cocharacter lattices of `T`. The ambient datum `P` has a finite root-index
type and is reduced.

`C.corootFace hA hj hP hR` constructs a `P.Base`, a subset `s` of that
base's simple indices, and the equality
`R.corootSpan ℤ = Submodule.span ℤ (P.coroot '' s)`.
The `SplitTorusCentralizerCorootFace P R` record exposes these as `base`,
`support`, `support_subset`, and `span_eq`. All spans are integral
submodules of the actual cocharacter lattice.

The root-range theorem `C.root_range_eq_zero` rewrites the model's
`relativeRoots_eq_pairing` using the two actual-root-datum predicates.
It identifies the centralizer roots with the ambient roots pairing to
zero against `C.cocharacter hA`. The constructor
`C.rootDatumEmbedding` uses the model's closed ambient maximal torus and
splitness to apply the proved `splitTorusWeylImageFinite`. Root inclusion
and the actual factorization through `j` then supply
`IsRootDatumOf.sameTorusSubgroupEmbedding`, including equality of the
integral coroots for matching roots.

The face constructor applies `rootZeroCorootFace` to the integral functional
`(latticePairing C.torus).flip (C.cocharacter hA)` on the character lattice.
The root-range identification and `SameTorusRootDatumEmbedding.corootSpan_eq`
first identify the centralizer coroot span with the span of all ambient
zero-root coroots. The adapted-base construction identifies this span with
the selected simple-coroot span. Transitivity supplies the record's equality.

The provenance is this composition of existing internal constructions.
No new external structural assertion is assumed. The constructor does not
require algebraic closedness or reductivity beyond the supplied model and
actual root data. It does not construct those root data, a torus of the
derived subgroup, or the comparison from its different cocharacter lattice.
Those remain necessary for
`SplitTorusCentralizerDerivedCorootComparisonStatement`.
