# Borel images of chamber model morphisms

For a nonarchimedean local field `F : Type u`, an affine group scheme `G`,
and a supplied `KPBuildingDatum G` satisfying `SatisfiesGroupAxioms`,
`reductiveImage_isGeometricBorel_iff_isChamber` proves that the actual
reductive image of an incident facet is a geometric Borel if and only
if that facet is a chamber. The universe `u` is arbitrary.

`chamberBorelImageInclusion` retains the actual schematic image inclusion
of the supplied chamber model morphism, together with its geometric
Borel property. Both its source and target are the supplied objects;
the underlying morphism is definitionally the existing
`reductiveImageInclusion`.

The generic helper `IsSolvableGroupScheme.map_of_surjective` passes
solvability through a scheme-surjective homomorphism locally of finite
type. After algebraic closure, surjectivity on rational points supplies
the quotient of the source's solvable point group.

`IsParabolicSubgroup.isGeometricBorelSubgroup_of_isSolvable` proves that
a solvable parabolic in a smooth connected affine group is a geometric
Borel. The parabolic's geometric Borel witness factors through its
smooth connected solvable source, so Borel maximality makes this factor
an isomorphism. Transport through the inverse identifies the
algebraic-closure inclusion as Borel, and geometric Borel descent
supplies the ground-field Borel property.

For a chamber, the proved torus criterion and the supplied represented
unipotent-radical quotient make the neutral special fibre solvable.
The actual reductive schematic image is parabolic by the supplied
parabolic correspondence. It is smooth and connected, hence
geometrically integral. Smoothness of the source supplies geometric
reducedness, making the schematic projection flat. Irreducibility of
the image makes this flat homomorphism surjective. Solvability passes
to the image, giving its geometric Borel property.

For the converse, use the given incidence's common apartment chart.
Choose a chamber above the upper facet in that chart. Transitivity of
the affine face relation makes this chamber incident above both
facets. The supplied opposite-order correspondence makes its Borel
image a subgroup of the assumed Borel image. The helper
`IsBorelSubgroup.range_eq_of_range_le` uses the represented factor
and Borel maximality to make this inclusion an isomorphism, so the two
all-test subgroup functors are equal. Injectivity of the supplied
parabolic correspondence then identifies the original upper facet
with the chamber.

This is an internal composition of the existing quotient, schematic
image, connectedness, solvability, Borel descent, facet-incidence and
chamber-torus results with the supplied KP axioms. It proves the second
clause of `FacetReductiveComparisons` without assuming that proposition.
The radical-preimage comparison and the full maximal pro-p proposition
remain separate obligations.
