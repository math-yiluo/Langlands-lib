# Geometry of actual inverse images under a supplied Levi retraction

Worker 1452. This internal construction supplies the ambient parabolic and its
all-test compatibility for the unchanged parabolic extension statement. It does
not supply the new geometric radical or the decomposition with the original
inner Levi.

For a supplied outer Levi decomposition `l : M ⟶ P`, `r : U ⟶ P` with
isomorphic Levi-first multiplication and normal `range r`, and an inner
parabolic `c : C ⟶ M`, the group is the actual pullback
`P ×_M C` along `leviRetraction l r hn`. With an outer parabolic `p : P ⟶ G`,
rational Levi data for `l` and geometric unipotent radical data for `r`,
`ambientParabolic` returns the composite of the pullback inclusion with `p`,
carrying proofs that it is parabolic, that its range is contained in `range p`,
and that its intersection with the original ambient Levi is exactly
`range (c ≫ l ≫ p)`. These are subgroup-functor statements on every relative
test scheme over an arbitrary field in the original universe.

The arbitrary-base helpers first show that the supplied multiplication
isomorphism persists under base change. A homomorphism that is identity on the
supplied Levi and kills the supplied radical is uniquely the Levi retraction:
decompose each test point by the original multiplication. This uniqueness
proves that the retraction commutes with arbitrary base change.

The Borel-preimage lemma uses the actual Levi retraction and its smooth,
geometrically connected unipotent kernel. The inverse image of a supplied
Borel is smooth and connected by pullback geometry, and solvable on geometric
points by the exact kernel and solvable quotient. For maximality, take the
smooth connected schematic image of any solvable closed overgroup in the
Levi. The original Borel factors into this image using its canonical section,
so Borel maximality makes that factor an isomorphism. Its inverse gives a map
from the whole overgroup back into the inverse image. The two closed
embeddings then cancel to prove that the original overgroup map is an
isomorphism.

To prove ambient parabolicity, base change to the algebraic closure. A Borel
contained in the inner parabolic pulls back to a Borel of the outer parabolic
by the preceding lemma. The outer parabolic contains an ambient Borel;
the published unconditional Borel conjugacy and Borel promotion results
therefore make the constructed Borel an ambient Borel. Its range factors
through the base change of `P ×_M C`, since the retraction commutes with base
change and the original Borel factors through `C`. Representability of the
closed subgroup range produces the actual factor homomorphism. Together with
closedness and smoothness of the original inverse image, this is precisely
the geometric Borel witness required by `IsParabolicSubgroup`.

The construction derives from the published actual Levi retraction,
subgroup-preimage, smooth connected image, solvability, Borel conjugacy and
Borel promotion interfaces. The containment and intersection proofs reuse
`LeviPreimage.range_ambient_le` and `range_ambient_intersection`; monicity
comes from the supplied closed subgroup maps. This is internal mathematical
preparation and introduces no structural-existence premise or dynamic
presentation.
