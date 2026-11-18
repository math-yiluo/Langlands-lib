# Lattice chains normalized by an extension field

This module develops the lattice-chain comparison used in Bushnell–Kutzko
1993, (1.2.1)–(1.2.4), printed pp. 24–25
(`bushnell-kutzko-1993-admissible-dual-gln`). Stability under the integer
ring of the extension follows from boundedness. The orbit of a vector
under nonnegative powers of an integral scalar lies in a finite module
over the base integers and hence in one member of the chain. A negative
shift would move a vector lying strictly between consecutive lattices
outside that bound.

An extension uniformizer shifts the chain by a positive number of
steps. This follows by factoring a base uniformizer as a unit times
a positive power of the extension uniformizer. `LatticeChain.extensionChain`
uses the original subsets with their extension-integer scalars. Its
endomorphism filtration at each integer index is the intersection of the
original step with the extension-linear endomorphisms.

For a nonempty finite extension-field basis, `subfieldBasisChain` takes
the integer span of the basis and all its rescalings by powers of the
extension uniformizer. This gives a chain over the base integers
normalized by all nonzero extension scalars. Applying a scalar to a basis
vector at index zero tests whether it is integral.
