# A nonzero cuspidal Jacquet module at an arbitrary source universe

This internal construction generalizes the published `RationalMinimalJacquet`
argument from source carrier `Type (max (u + 1) v)` to source carrier `Type v`,
where the field/group universe `u` and source universe `v` are independent.
Worker 1784 reuses the proof of Worker 78 and the original relation-span proof
material of Worker 379. No new original-literature translation is claimed.

`exists_nontrivial_isLeviCuspidal_jacquet_arbitraryCarrier` proves that a
nontrivial smooth complex representation of the actual rational-point group
has a standard index `I` whose actual normalized Jacquet module is nontrivial
and satisfies `IsLeviCuspidal` for the proper standard tests inside the same
Levi. `nonzeroCuspidalJacquetIndexArbitraryCarrier` chooses such an index;
its subtype property contains both conclusions.

The hypotheses are exactly the rational minimal-Jacquet hypotheses: a
nonarchimedean local field, a connected reductive group, a maximal split torus,
a generic cocharacter, the standard-cocharacter and Levi-intersection
statements, a relative-root system, closed standard unipotent radicals and
Levis, and local compactness and the nonarchimedean-group property for the
canonical rational-point topology. The affine and monomorphism instances are
explicitly available to form the standard families. No finiteness condition
on the representation is assumed.

The implemented proof repeats the minimum-cardinality argument at the smaller
carrier universe. The full standard unipotent radical is trivial, so a
nonzero vector remains nonzero in its Jacquet quotient. Choose an index of
minimal cardinality among the nonzero Jacquet modules. Each proper standard
test inside its Levi has a strictly smaller ambient index and therefore a
zero ambient Jacquet module. The published relation-span lemmas carry this
vanishing to the inner Jacquet module. Their inputs come from the standard
unipotent product, normalizer inclusion, and compact-limit regularity. The
latter makes the outer inverse-half modulus trivial on the finer radical.
Closedness of the chosen Levi supplies its local compactness.

This construction is useful for detecting a nonzero subrepresentation whose
carrier remains in `Type v`. It does not construct a cuspidal projection, a
finite induced-cuspidal embedding, a whole-category splitting, or a proof of
`RationalCuspidalInducedEmbeddingStatement`.
