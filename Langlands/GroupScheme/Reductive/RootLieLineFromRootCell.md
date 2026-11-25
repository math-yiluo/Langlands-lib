# Root Lie lines from a supplied open root cell

Internal derived construction; this is a supporting
module, and does not prove `SplitRootLieLineStatement` without further inputs.

`RootCellLie.lineEquiv` constructs a linear equivalence
`k ≃ₗ[k] weightSpace i α`. Its hypotheses are a field `k`, an affine locally
finite type group scheme `G`, a commutative split torus `T`, a homomorphism
`i : T.toGrp ⟶ G`, a nonzero character `α`, and two supplied maps
`xp xm : VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G`. Conjugation by `T`
on these maps must agree on every test scheme with the scalar actions of `α`
and `-α`, respectively. The multiplication map `xm · i · xp` must be an open
immersion, and `weightSpace i α` must be nonzero. No existence assertion for
these maps is made, and no maximality or reductivity is required by this module.

The auxiliary `exists_lie_decomposition` works over any commutative base ring
and any test algebra in the same universe. All four groups must be affine and
the multiplication chart must be an open immersion. It lifts an actual
identity-reducing dual-number point through that chart, using
`Lie.exists_dualNumberLift_of_openImmersion`, with the triple identity as the
reduced lift. The three projections reduce to identity and supply the three
summands of its actual Lie vector.

`weightSpace_eq_range` identifies the `α` weight space with the differential
image of `xp`. The scalar coordinate calculation converts the supplied
all-test action laws to `VectorGroup.IsTorusEquivariant`. Its published
`lie_range_le_weightSpace` lemma places the negative and positive differential
images in weights `-α` and `α`. The torus differential is in weight zero.
The internal weight decomposition of a split torus makes the `α` space
disjoint from the sum of the other two spaces. Here `-α ≠ α` follows from
torsion freeness of the character lattice, including in characteristic two.
Thus the first two summands of an `α` vector vanish together.

`finrank_weightSpace_eq_one` bounds the dimension of that differential image
by the dimension one of the source Lie algebra, using the actual
`RelativeRoot.vectorLieCoordinates` equivalence. The nonzero-space premise
and finite dimension of the ambient Lie algebra give the reverse positive
bound. `lineEquiv` chooses the resulting linear equivalence by the ordinary
finite-dimensional linear algebra theorem.

The provenance is the internal tangent and weight-space argument just
described, assembled from the named Library lemmas and Mathlib linear algebra.
It is not a transcription of an external theorem. The source and target
statements retain the supplied cell as a hypothesis. Compilation was checked;
the declaration type/value independence audit and the exact-target proof are
not part of this module.
