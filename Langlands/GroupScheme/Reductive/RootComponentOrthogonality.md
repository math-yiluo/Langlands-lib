# Orthogonality and exclusion of mixed roots between coordinate components

For a supplied `RootComponentCoordinates M`, every root has a nonzero full
character coordinate, necessarily in its specified Cartan component. The
construction `rootCoordinateWitness` chooses one such simple index.

If two roots have different component labels, every integral combination
with both coefficients nonzero is nonzero and is not a root. The proof uses
the two chosen coordinates: one detects the first summand and annihilates the
second; the other detects the second and annihilates the first. A root with
both coordinates nonzero would have to belong to both components, contrary
to the supplied support property.

This also proves that the Cartan pairing of two roots in different components
is zero. Otherwise their reflection would be a mixed combination with two
nonzero coefficients, hence could not be a root. Consequently such a
reflection fixes the original root index.

These are internally derived consequences of the integral coordinate-support
interface, injectivity, nonzero roots and the root reflection identity. They
prepare the root-subgroup commutation step in the component-centralizer route
motivated by Conrad, *Reductive group schemes* (2014), Proposition 6.4.4,
pp.232–233. No group-scheme commutation or factorization is asserted here.
