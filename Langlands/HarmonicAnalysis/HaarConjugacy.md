# Haar scaling under continuous group conjugacy

`Langlands.Geometric.haarChar_eq_of_conjugacy` states that automorphisms of
locally compact topological groups have the same Haar scaling character
when they are intertwined by a continuous group isomorphism. Both groups
carry Borel measurable structures. No finite total Haar mass is assumed.

The proof pushes a regular Haar measure through the isomorphism, transports
the scaling identity, and applies uniqueness of the Haar scalar factor.

Integration moves this existing theorem and its proof unchanged from
`Langlands.Representation.Geometric.ParabolicOrbitHaarTransport` to the
harmonic-analysis layer, preserving its public name. The orbit transport
module and `MirabolicProductMinusRightPsiGroups` now import this one copy.
