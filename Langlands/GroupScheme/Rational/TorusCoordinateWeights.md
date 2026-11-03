# Actual eigenfunctions and corepresented homogeneous coordinates

This internal comparison identifies the published corepresented homogeneous
coordinates with eigenfunctions for the original actual automorphic action.
It retains arbitrary universe `u`.

For an arbitrary corepresented group-valued algebra functor over a commutative
ring, the coaction identity defining a homogeneous coordinate is equivalent
to its eigenfunction identity on every algebra, every family of units and
every group point. The forward direction is the existing evaluation formula.
For the converse the proof evaluates the asserted identity at the universal
units and universal point over the group algebra. The resulting monomial is
exactly the homogeneous coaction identity.

For an affine group over a field acted on by a split commutative group scheme,
the chosen split-torus isomorphism identifies exponent vectors with the existing
actual character lattice through `PointedCoordinateWeights.characterEquiv`.
Character evaluation on `AutomorphicAction.torusPoint` is the exponent value.
Every actual acting point is recovered by the action-coordinate bridge, so
the homogeneous-coordinate identity is equivalent to
`CoordinateWeights.IsEigenfunction` in CGP's convention on all coefficient
algebras. Thus the two constructions give equal submodules of the original
`Lie.coordinateAlgebra G`. Their augmentations agree definitionally.
`homogeneousWeightSpaceEquiv` is the resulting canonical linear equivalence
between these two submodules, retaining their original coordinate vectors.

The provenance is internal composition of the universal-unit coaction formulas,
the published character-lattice point formulas and the original action-coordinate
bridge. This comparison makes no realization, connectedness or unipotence claim.
