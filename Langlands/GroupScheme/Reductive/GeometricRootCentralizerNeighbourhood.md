# Actual geometric root reflections and centralizer neighbourhoods

This internal construction produces an actual good open in an arbitrary affine
base from forward root data at one original geometric fibre. The supplied
standard torus is closed, and its image in that original geometric identity
component is self-centralizing. Root negation, reducedness along each root line,
one-dimensional actual root weights and actual reflection points are explicit
inputs. Their existence and the initial torus lifting remain obligations of the
general openness proof. This module does not prove the final openness statement.

For a fixed integer cocharacter vector, `geometricIdentityTransporterPoint`
starts with an actual point of the original ambient geometric identity
component. The point transports the actual standard torus by an integral
automorphism that fixes the actual cocharacter over that geometric field.
Precomposing its all-test transporter equation with the cocharacter proves
membership in the actual cocharacter centralizer. The existing represented
centralizer comparison identifies that subgroup inside the ambient identity
component with the identity component of the actual relative centralizer's
actual geometric fibre. Its inverse point equivalence therefore constructs a
point of this latter component. No assumption that an arbitrary centralizer
point lies in its identity component is made.

`geometricIdentityTransporterPoint_comp` recovers exactly the original point
after the specified actual inclusion. Monicity reflects the all-test transporter
equation for the centralizer's actual torus; this is
`geometricIdentityTransporterPoint_isTransporter`. The fixing assumption is
needed only over the specified original geometric field. No relative
automorphism-fixing equation is required on the whole original base.

`exponentWeightRank_eq_of_dot_eq_zero` compares an actual surviving relative
centralizer weight rank with its ambient rank. It combines the differential
weight equivalence for the actual centralizer inclusion with the comparisons
between relative stalk ranks and weights in the chosen algebraic closures of
the actual residue fields.

`GeometricRootReflectionData` packages the actual original-fibre inputs for a
root: an integral automorphism inverting the root, its fixing equation for the
previously constructed generic annihilating cocharacter, an actual ambient
geometric identity-component point, and its all-test transporter equation.
Packaging the data asserts no existence theorem.

`rootCentralizerReductiveNeighbourhood_of_geometricReflection` chooses the fixed
integer vector already constructed from the specified root and the finite
actual original root set. Its actual relative cocharacter centralizer is smooth
affine. Self-centralization is inherited from the ambient torus. The supplied
root negation and reducedness along this root line identify the complete
actual centralizer root support as the root and its negative. The weight-rank
comparison gives rank one for both surviving weights. The factored geometric
point satisfies the required transporter equation inside the centralizer's
actual geometric identity component. Applying
`rankOneIdentityComponentReductiveNeighbourhood_of_geometricTransporter`
constructs a good open for this actual relative centralizer.

Finally,
`identityComponentReductiveNeighbourhood_of_geometricRootReflections`
enumerates the finite actual roots of the original geometric identity
component. For each root it constructs the preceding centralizer good open.
The existing finite-centralizer neighbourhood construction intersects these
opens with the actual root-profile constancy open and the actual
self-centralizing torus locus. At each point of this intersection its
rootwise centralizer witnesses annihilate every possible weight of every
smooth connected normal unipotent subgroup, proving connected reductivity
of the actual ambient geometric identity component.

The provenance is internal composition of the published actual relative
centralizer, geometric profile and radical-detection constructions, the
geometric-transporter rank-one neighbourhood constructor, and Worker 1683's
fixed-cocharacter transporter lemma. The construction retains arbitrary
commutative rings and arbitrary universe `u`; the base may be nonreduced or
nonnoetherian and the ambient fibres may be disconnected.
