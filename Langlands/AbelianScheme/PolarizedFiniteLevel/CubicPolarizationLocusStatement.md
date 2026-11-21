# The cubic polarization locus of a projectively embedded abelian scheme

`Langlands.AbelianScheme.PolarizedFiniteLevel.CubicPolarizationLocusStatement`
fixes an abelian scheme `A` over a locally noetherian base `S` and a closed
embedding into relative projective space over `S`. It asks for an immersion
`j : Z ⟶ S` such that a test map `t : T ⟶ S` from a locally noetherian scheme
factors through `j` exactly when the pullback abelian scheme admits a
polarization of degree `d²` with the required cubic bundle. The bundle to
compare is the pullback of the given embedding's `𝒪(1)`.

`ExistsCubicPolarization` includes a dual witness for the test abelian scheme,
the Library's `IsPolarization` and `HasDegreeSquare` predicates, and an
isomorphism from the pulled-back line bundle to the cube of the diagonal
Poincaré bundle tensored with a pullback from `T`. The twist expresses the
normalization along the identity in Proposition 6.11, since the diagonal
Poincaré bundle is trivial there. This formulation starts with the abelian
scheme already constructed and places no level conditions on it.

This is the degree-specific form of the polarization step in Mumford, Fogarty
and Kirwan, *Geometric Invariant Theory*, 3rd ed. (1994), Proposition 6.11 and
the proof of Proposition 7.3, step (V). The source cuts out the polarized cubic
condition by a closed subscheme. The prescribed degree condition is included
in the target. The native rank of a finite flat isogeny is locally constant,
so a degree restriction on a family of polarizations is open and closed.

The registered source is
`provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f`,
SHA-256 `3eed7c31fd64936e20a41d85c85ebaeebc3f2631b01f561417b85bdf33b1af16`,
printed pp. 121–123 and 133–134 (PDF pp. 134–136 and 146–147).
