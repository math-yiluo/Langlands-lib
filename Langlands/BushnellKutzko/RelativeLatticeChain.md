# The lattice chain over a normalizing subfield

`LatticeChain.relativeLatticeChain` implements the lattice-chain step
of Bushnell–Kutzko (1993), `bushnell-kutzko-1993-admissible-dual-gln`,
(1.2.1)–(1.2.2), printed pages 24–25. The extension \(E\) acts on
the original vector space, its units stabilize the original chain,
and its valuation ring consists of the elements integral over the
base integer ring. `isIntegral_iff_mem_spectralInteger` verifies the
last condition for the spectral valuation of a finite extension using
`LocalGalois.integral_iff_mem_spectralIntegers`. The resulting chain
keeps the original lattice subsets, and its endomorphism filtration
restricts the original filtration to endomorphisms linear over \(E\).

The shift of a scalar unit is the integer shift of its action on the
original chain. Shifts add under composition. The powers of an integral
scalar applied to a fixed vector belong to the image of a finitely
generated module over the base integer ring, so they lie in a common
lattice. Taking the vector in the difference of consecutive lattices
rules out a negative shift for that scalar. Applying this argument to
an integer unit and its inverse gives shift zero. Factoring a base
uniformizer into a power of an extension uniformizer times an integer
unit proves that the extension uniformizer has positive shift.

Each original lattice is stable under the extension integer ring.
Its base integer generators also generate it over the extension
integer ring, and its span over the extension field is the whole space.
The positive shift of the extension uniformizer gives the period of
the relative chain.
