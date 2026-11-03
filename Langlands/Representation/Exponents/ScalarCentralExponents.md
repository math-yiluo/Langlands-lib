# Central exponents under embeddings into a scalar central action

This is an internal deduction for complex representations of an arbitrary
topological group. The group and both carrier universes are independent.
The central exponents are the existing `IsCentralExponent`: the character
has open kernel on the full abstract center, and its uniform generalized
central-character subrepresentation is nonzero.

`isCentralExponent_of_injective` proves that an injective actual intertwiner
preserves this predicate. The open-kernel condition is the same on both
sides. The published `map_mem_generalizedCentralCharacterSpace` carries a
generalized vector into the target space; if that target space were zero,
injectivity would force the source space to be zero.
`isCentralExponent_equiv_iff` applies this in both directions of an actual
equivariant equivalence.

`centralExponent_eq_of_scalar_injective` additionally assumes that the
target has the displayed scalar action of a specified full-center
character. It proves that every exponent of the source equals that
character. A nonzero generalized vector has a nonzero image under the
embedding. This image is an ordinary eigenvector for the scalar character
and a generalized eigenvector for the exponent. For each central element,
the published `eq_of_eigen_of_mem_genEigenspace` equates the two eigenvalues;
extensionality then equates the characters.

The proof uses no admissibility, irreducibility, finite length, spectral
decomposition, classification, character independence, geometric lemma,
adjointness or cuspidal-support theorem. No new literature assertion is
introduced. The scalar-action premise is retained; this pair does not
produce a scalar character for an arbitrary irreducible representation.
