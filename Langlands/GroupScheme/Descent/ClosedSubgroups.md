# Effective descent of invariant affine closed subgroups

This internal construction works in arbitrary universe `u` with actual schemes,
group schemes, and equality of represented subgroup images on every relative
test scheme. In particular, it includes nonreduced and nonaffine tests. No new
external literature assertion is used.

Let `p : S ⟶ B`, let `D : Descent.Datum p G` be actual ambient descent data,
and let `i : H ⟶ G` be a closed subgroup. Assume that composing the first
pullback inclusion with the supplied ambient overlap isomorphism has the same
all-test image as the second pullback inclusion.

`Datum.closedSubgroupOverlap` uses the published source comparison for equal
closed subgroup images to construct an actual isomorphism between the two
pullbacks of `H`. `closedSubgroupOverlap_fac` proves its commuting equation
with the inclusions. No source overlap isomorphism is an additional input.

`cocycle_of_closedSubgroup_lift` proves that any source overlap isomorphism
satisfying this commuting equation has a cocycle. Pull the commuting equation
back to the three pairs of coordinates. The ambient cocycle identifies the
composite and direct source transports after the third inclusion; this
inclusion is closed and hence monic, so cancellation identifies the transports.
`Datum.closedSubgroup` packages the constructed overlap with this proved
cocycle. `compatible_closedSubgroup` supplies compatibility of the original
inclusion with the constructed data. These steps require no flatness,
affineness or surjectivity assumptions on the base morphism.

For closedness reflection, assume that `B`, `S` and the underlying schemes of
two group schemes over `B` are affine, and that `p` is flat and surjective.
`IsClosedSubgroup.of_baseChange_of_isAffine` proves that a homomorphism is a
closed subgroup inclusion whenever its pullback is one. The proof constructs
the actual pullback square for the homomorphism and applies the published
`Langlands.AlgebraicGeometry.isClosedImmersion_of_isPullback_of_affine_fpqc`.
That theorem reflects surjectivity of the map of affine coordinate rings by
faithfully flat ring descent. Thus closedness of the original arrow is proved,
rather than included as an extra descent hypothesis.

Finally, take an affine group scheme `C` over affine `B` and a closed subgroup
`i : H ⟶ p*C` over affine `S`. Suppose `p` is flat and surjective and the
all-test image equality above holds for the canonical ambient overlap of `C`.
`IsClosedSubgroup.exists_descent_of_overlap_range_eq` constructs:

- an actual affine group scheme `H₀` over `B`;
- an actual closed subgroup inclusion `j : H₀ ⟶ C`;
- an actual isomorphism `e : p*H₀ ≅ H` satisfying
  `(baseChange p).map j = e.hom ≫ i`.

Closedness of `i` in the affine pullback of `C` first supplies affineness of
`H`. The preceding construction gives its actual descent datum and inclusion
compatibility. The published `Datum.affineSolution` then constructs the
affine descended group, and `Datum.affineHomTo` constructs its map to `C`.
Their recovery equation proves the displayed identity. The pulled-back arrow
is therefore the composite of an isomorphism with the original closed
inclusion; the reflection theorem proves that the descended arrow is closed.
The input contains neither a solution nor an effectivity or closedness
reflection premise.

This is a prerequisite for rational unipotent-radical descent. The overlap
image equality is still an explicit input: this pair does not derive it from
Galois automorphism invariance, and it assumes no finite-Galois component
decomposition. Radical existence, transport of radical properties through the
constructed descent, radical splitness and maximal-torus conjugacy remain
separate obligations. There is no restriction to perfect or infinite fields
or to characteristic zero; the construction is not restricted to field bases.
