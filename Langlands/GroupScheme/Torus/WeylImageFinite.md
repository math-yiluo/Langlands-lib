# Finite full Weyl images of closed split tori

Author: Worker 1375. The published representation-weight finiteness and
Weyl-image transport inputs are due to Worker 1283.

This internal assembly constructs
`Langlands.GroupScheme.weylImageFintypeOfClosedSplitTorus`, a finite enumeration
of the actual subgroup `weylImage i` for any closed split torus in an affine
algebraic group over an arbitrary field. It also proves
`splitTorusWeylImageFinite`, whose type is the unchanged published proposition
`SplitTorusWeylImageFiniteStatement.{u}`.

For a standard split torus, choose a finite-dimensional closed matrix
representation of the ambient group with `affineLinearEmbeddingStatement`.
Both the torus embedding and the representation are closed immersions of
schemes, hence their composite is a monomorphism. The coefficient matrices
of the representation on the universal torus point have finite exponent
support, and this monomorphism makes the exponents with nonzero coefficient
matrix generate the whole integral character group. The published
`NormalizerRepresentationWeights.weight_ne_zero_normalizingAut` proves that
each actual normalizing point preserves this set: its invertible base matrix
intertwines the original and transformed weight matrices. The exponent action
used there is definitionally the same action used in
`RepresentationWeightWeylFinite.finite_weylImage_of_weight_stable`.

Applying that theorem proves `finite_weylImage_standard`. Its finite-generator
argument restricts the image action to permutations of a finite generating
set of actual characters. Agreement on this set forces agreement on the
entire lattice. The conclusion therefore concerns the full published Weyl
image, including directions outside the root span.

The published `splitTorusWeylImageFinite_of_standard` then transports the result
along a chosen split-torus isomorphism. Its transport is an actual
multiplicative equivalence of the two Weyl-image subgroups, obtained by
conjugating their integral character automorphisms. It uses the existing
normalizer-point transport and its action comparison. Finally,
`weylImageFintypeOfClosedSplitTorus` applies classical finite enumeration to
this proved finite actual subgroup.

The quantifiers allow every field universe and characteristic, imperfect
fields, disconnected or nonsmooth ambient groups, nonmaximal split tori and
rank zero. No smoothness, reductivity, connectedness or root datum is used.
All geometric and action comparisons are imported proved results; no
finiteness or support-stability premise remains. This is a supporting unit
for the central-isogeny root-datum task: that task's root comparison,
supplied-coroot compatibility and final isomorphism criterion remain separate.

The construction and proof are derived internally from the named Library
interfaces. The argument uses faithful representation weights, rather than
the identity-component normalizer/centralizer route described in the paired
Markdown of `Torus.WeylImageFiniteStatement`.
