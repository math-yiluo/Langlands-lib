# Finite presentation of multiplicative-type normalizers

Let `G` be a group scheme locally of finite presentation over an arbitrary
base scheme, and let `i : H ⟶ G` be a closed inclusion of a group of
multiplicative type. The theorem
`normalizer_range_locallyOfFinitePresentation_of_multiplicativeType` shows
that any homomorphism representing the full normalizer on all relative test
schemes is locally of finite presentation.

Over an affine base with diagonalizable `H`, its coordinates form a free
module over the base ring. The inclusion is locally of finite presentation
because the structure morphism of `H` is locally of finite presentation and
that of `G` is locally of finite type. Pulling the inclusion back along
inverse conjugation gives the closed product locus. Apply
`ClosedFactorizationFinitePresentation.model` to construct the locus of
ambient points that conjugate `H` into itself. Its inclusion and the
inclusion obtained by inversion are both locally of finite presentation.
Their intersection represents the full normalizer, since its points
satisfy both conjugation inclusions on every test and its refinements.
The comparison with the supplied representative transfers local finite
presentation to its inclusion into `G`.

Pull the affine and splitting covers of the base back to the ambient
scheme. The normalizer functor and its representation commute with these
base changes, so fppf locality on the target descends local finite
presentation to the original inclusion.

`relativeTorusFinitelyPresentedNormalizerModel` applies this argument to
the actual closed representative given by `relativeTorusClosedNormalizerModel`.
It supplies local finite presentation of both the inclusion and the
structure morphism. This internal construction uses the Library's
factorization, diagonalizable coordinates, and fppf descent results.
