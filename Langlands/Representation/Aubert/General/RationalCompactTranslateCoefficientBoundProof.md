# Compact translates of the actual rational coefficient bound

`rationalCompactTranslateCoefficientBound` proves the complete
`RationalCompactTranslateCoefficientBoundStatement` at independent universes
`u`, `v` and `w`.

The proof applies `rationalLatticeCoefficientDecay` to extract the common
compact-open normal basis and, for the given finite ray family, the actual
full-center Levi points with their uniformizer-power identities. These choices
precede all translating sets and smooth coefficient pairs.

For a smooth functional and vector, smoothness provides two open fixing
subgroups. The identity-neighborhood basis supplies a member contained in their
intersection. Its openness makes it an `OpenSubgroup`.
`fixedVectors_antitone` restricts both fixing conditions to this member. The
actual lattice coefficient bound then supplies positive radii, their strict
weighted-square inequalities and a positive coefficient constant for this
unrestricted input pair.

Finally, `compactTranslateLatticeBound` extends these pairwise bounds uniformly
over both compact translating sets and the finite middle set. Its weights are
the unchanged inverse actual unipotent Haar moduli at the already chosen central
points. The generic adapter uses finite compact orbits and attained finite
maxima; it applies also to empty ray families and empty translating sets.

The additional argument is an internal composition and uses only smoothness,
neighborhood bases and fixed-vector order. Its representation-theoretic input is
`rationalLatticeCoefficientDecay`, whose proof obtains finite-dimensional
compression spectra from admissibility and the actual normalized Jacquet
exponent hypothesis. No classification, geometric lemma, adjointness, character
independence or cuspidal-support theorem is used by this composition. It leaves
basis existence, chamber covers, quotient-volume estimates and integration to
the complete criterion.
