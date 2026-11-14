# Assembling a multiplicity-one signed weight support

This internal algebraic prerequisite assembles the hypotheses needed by the
signed-weight dimension count. Its main conclusion is conditional on an
additively generating symmetric finite support, positive and sign-symmetric
multiplicities, and a bound on sums of multiplicities over nonopposite
subfamilies. It does not establish these geometric inputs for an isometry group.

`mem_signedWeights_iff` identifies membership in the finite signed support of an
integral basis with being a basis vector or its negative. The proof uses the two
units of the integers.

`exists_basis_of_representatives` accepts a finite set `P` contained in a
symmetric finite support `A`, with every nonzero member of `A` represented in `P`
up to sign. The support generates an arbitrary additive commutative group `L`.
Multiplicities on `P` are positive, their sum is at most `r`, the integral rank
of `L` is `r`, and multiplicities agree at the negative of every member of `P`.
The earlier `SignedWeightBasis` lemmas give cardinality equal to rank, an
integral basis consisting of exactly the representatives, and multiplicity one
on `P`. Reindexing this basis by `Fin r` preserves its actual vectors. Coverage
and symmetry identify `A.erase 0` with its signed support; symmetry of
multiplicities proves multiplicity one on both signs. Zero may either occur in
`A` or be absent.

`exists_nonopposite_half` applies the published
`HermitianWeights.exists_nonopposite_subfamily` to the subtype of members of a
finite support in the coordinate lattice `I → ℤ`. Taking the finite image of
the chosen subtype indices gives a subset with no pair adding to zero and
covering every nonzero weight up to sign. That published finite maximality
argument already handles an empty support and an empty coordinate index.

`exists_basis_of_nonopposite_bound` combines these constructions. The coordinate
index `I` is finite, its cardinality is `r`, every support multiplicity is
positive and agrees with its negative, and every nonopposite subfamily has
multiplicity sum at most `r`. Choosing the preceding half supplies precisely
the inputs to `exists_basis_of_representatives`. The result is an integral
`Fin r` basis with exact nonzero signed support and multiplicity one for every
signed index. This supplies the algebraic passage from a geometric dimension
bound and rank equality to the signed decomposition required by
`SignedWeightCount` and `SignedWeightTransport`.

`basisOfNonoppositeBound` chooses this basis with precisely the same hypotheses;
`basisOfNonoppositeBound_spec` records its exact support and multiplicity-one
properties. The choice adds no further premise.

The provenance is internal: finite support selection reuses the published
Hermitian-weight selection lemma, while the equality, basis and multiplicity
arguments reuse `SignedWeightBasis`; the finite signed support is that of
`SignedWeightCount`. No theorem about isometry groups or maximal split tori is
claimed here, and no field or characteristic hypothesis is introduced.
