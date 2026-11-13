# The full-support endpoint of the actual smooth Aubert complex

Internal construction by Worker 3640, specializing the published
`Complex.terminalIsoOfDegreeEqZero`, `Complex.terminalProjection_zero_injective`
and `Complex.initialTerminalMap_bijective` from
`RationalFixedLeviComparisonProof`. The construction concerns the same actual
normalized complex as `CanonicalRationalComplex`.

`canonicalRationalSharpUnivIso` identifies the retained terminal cokernel
functor for the full actual simple-root subset with the identity functor on
all smooth complex representations. The removed-root terminal degree is
`|S| - |S| = 0`. The incoming boundary in this degree is zero. Published
full-root endpoint theorems identify the initial object with the input,
and the actual quotient projection then gives the natural isomorphism.
Its construction uses `Complex.terminalIsoOfDegreeEqZero`, whose degree-zero
inverse is the initial map followed by the terminal projection.

The two intrinsic laws state injectivity of this degree-zero quotient
projection and bijectivity of the literal composite
`canonicalRationalTerminalProjection … E 0` after
`canonicalRationalInitialMap … E`. They specialize the corresponding
published generic laws.

All three declarations take the same arbitrary nonarchimedean local field,
actual connected reductive group, maximal split torus, generic cocharacter
and arbitrary order of the actual simple roots as the canonical complex.
Topology, local compactness, the nonarchimedean group structure, root
finiteness and all subgroup structure are supplied internally by the same
published proofs. Field and module universes are independent, and the
carrier universe is `max (u + 1) v`. There is no finite-length,
admissibility or support-category premise. Empty simple-root sets are
included.

This is the full-support endpoint of the construction, motivated by the
retained-cokernel convention of Aubert's erratum (1996), p.4690 Remark (1).
It makes no exactness claim at positive degree and does not prove the
associated-Levi comparison or any irreducibility or double-Sharp statement.
The provenance is the named published construction and intrinsic laws;
no additional literature-derived theorem is introduced.
