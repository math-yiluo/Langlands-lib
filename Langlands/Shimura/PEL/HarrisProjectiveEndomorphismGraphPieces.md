# Affine endomorphism pieces indexed by the graph polynomial

Let `B` be an abelian scheme over an affine base, with an invertible
module `L` whose sections give a closed projective immersion.
`projectiveEndomorphismGraphPieces` retains the graph-polynomial
characterization of the open pieces from
`GoodReductionJacobian.RelativeGroupLaw.exists_homScheme_represents_hilbertPieces_of_closedImmersionBySections`.
It uses `AffineHomSchemePieces.natIso` for the actual relative
endomorphism functor on all affine tests. The resulting scheme is
separated, locally of finite type and formally unramified.

The polynomial-indexed opens are disjoint and cover the scheme.
Each is closed in the scheme and quasi-compact over the base.
`ProjectiveEndomorphismGraphPieces.range_subset_iff` identifies which
open contains the image of the morphism classifying a given actual
endomorphism on an affine test. The condition is eventual evaluation
of the indicated polynomial by the dimensions of sections of powers
of the exterior product of `L` with itself on the geometric graph.
The first projection identifies that graph with the test abelian
scheme and the second projection is the given endomorphism.
To identify the two classifying maps, the proof uses
`AffineHomSchemePieces.homEquiv_left` and naturality along the affine
test's isomorphism to the spectrum of its coordinate ring.
