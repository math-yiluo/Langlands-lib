# The locally closed locus of cubic polarizations of prescribed degree

`Langlands.AbelianScheme.PolarizedFiniteLevel.cubicPolarizationLocus` proves
`CubicPolarizationLocusStatement` in every universe. The theorem gives an
immersion of the locally noetherian base and its factorization criterion for
every locally noetherian test scheme.

The [assembly](CubicPolarizationLocus/Assembly.md) first uses the full finite
flat kernel of multiplication by six to cut out the closed locus where the
Mumford map of the embedding bundle is divisible by six. The
[positive-multiple descent theorem](AlgebraicallyClosedFieldPolarizationDivisionProof.md)
provides an ample Mumford presentation of the divided map on each geometric
fibre. These presentations make the divided map a polarization on the
divisibility locus.

The second closed condition equates the normalized classes of the embedding
bundle and the cube of the polarization's diagonal Poincaré bundle. Equality
of the normalized classes gives exactly the twist by a line bundle from the
test base. The open condition fixes the native isogeny rank at the identity
to `d²`. Uniqueness of division by six and compatibility of the dual and the
diagonal bundle with pullback give the factorization criterion with arbitrary
dual witnesses.

The two closed conditions follow Mumford, Fogarty and Kirwan, *Geometric
Invariant Theory*, 3rd ed. (1994), Proposition 6.11 and step (V) of the proof
of Proposition 7.3. The registered source is
`provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f`,
SHA-256 `3eed7c31fd64936e20a41d85c85ebaeebc3f2631b01f561417b85bdf33b1af16`,
printed pp. 121–123 and 133–134 (PDF pp. 134–136 and 146–147).
