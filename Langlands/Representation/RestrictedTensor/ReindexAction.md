# Naturality and actions for actual restricted tensor reindexing

This internal construction uses the actual direct-limit reindexing in
`RestrictedTensor.Reindex`, the factor maps in `RestrictedTensor.Maps`, and
the actual restricted-product action in `RestrictedTensor.Action`. It makes
no new original-literature identification.

The coefficient field, source and target index types, group carrier universe,
and two local vector carrier universes are independent. No topology or
finite-dimensionality of the vector carriers is assumed.

`reindex_preserves` pulls an almost-everywhere reference identity back along
the index equivalence. `reindexMap_natural` proves that factor maps commute
with the canonical reindexing maps. It permits different source and target
exceptional sets and reference families and does not require nonzero
references. Its proof uses cofinal finite stages containing the source map
bound and the inverse image of the target map bound. Every tuple is the
pullback of a tuple on the mapped finite set. The exact elementary-tensor
formulas on both sides then agree.

`reindexGroup` is the coordinate pullback homomorphism from the actual
cofinite restricted product of the groups `G j` relative to `H j` to the
restricted product of `G (q i)` relative to `H (q i)`. Its coordinates are
exactly `g (q i)`. The index equivalence preserves the cofinite filter, so
these coordinates satisfy the actual restricted-product condition.

`reindex_reference_fixed` proves reference fixedness outside `E` from
fixedness outside `E.map q.toEmbedding`. The genuine
`reindexRepresentationEquiv` has source the representation on the pulled-back
tensor family, precomposed with `reindexGroup`, and target the original
family's representation with mapped exceptions. Its vector map is exactly
`reindexMap`; the explicit nonzero-reference hypothesis outside the mapped
exceptional set is used by its underlying linear equivalence. Naturality
applied to the local operators proves equivariance.

This supplies algebraic action compatibility for the existing tensor spaces.
It asserts no topology on the tensor product, automorphic occurrence, or
factorization of arbitrary representations.
