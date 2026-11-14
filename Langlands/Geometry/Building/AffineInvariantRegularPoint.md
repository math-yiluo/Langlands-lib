# Regular points along invariant affine directions

This internal geometric construction uses the published real affine-root
arrangement, facet, and closure definitions. It applies in arbitrary universes
to an affine torsor, a locally finite reflection arrangement, and an arbitrary
indexed family of affine equivalences. No group law on the index is needed.

`IsLocallyFiniteReflectionArrangement.exists_regularPoint_in_subspace` takes
a point `p` and a real submodule `W`. For each ordinary root vanishing at `p`,
it requires a vector in `W` on which the root's derivative is nonzero. It
produces a regular point `x` with `x -ᵥ p ∈ W` and with `p` in the weak-sign
closure of the facet through `x`.

The proof takes the derivatives of the roots vanishing at `p`. This is a
finite subset of the arrangement's derivative roots. Restricting these
functionals to `W`, the finite union of proper linear kernels lemma
`Module.Dual.exists_forall_ne_zero_of_forall_exists` gives one vector on which
all of them are nonzero. The published `eventually_sign_smul_vadd` supplies a
positive scalar small enough to preserve every root sign that was nonzero at
`p`. Roots initially zero become nonzero along the chosen vector. These two
facts prove regularity and closure incidence, respectively.

`IsLocallyFiniteReflectionArrangement.exists_regularPoint_fixed` takes a
point fixed by every member of the supplied affine family. Its nonvanishing
premise requires each root through that point to have a nonzero value on
some vector fixed by every linear part. The proof uses the submodule of
common fixed vectors in the preceding theorem. The resulting point is
regular, remains incident to `p`, and is fixed by the entire affine family.

`invariantRegularPoint` chooses such a point as a subtype retaining all
three properties. `image_facet_invariantRegularPoint` additionally assumes
that every affine equivalence preserves the root arrangement. The published
`image_facet` theorem and pointwise fixedness then prove invariance of the
whole ordinary sign facet.

The construction is an internal prerequisite for the supplied-special-apartment
chamber problem. Its root nonvanishing premise is explicit and remains to be
established from the arithmetic and residual-group hypotheses in that
application. This file does not assert that a fixed point alone can be
perturbed to a regular fixed point. It adds no interpretation of external
literature: its provenance is the elementary subspace refinement of the
published proof of `exists_regularPoint_closure` in
`AffineWeylFacetFixing`, followed by affine equivariance.
