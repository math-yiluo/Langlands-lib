# The common equation bound for cubic embeddings

`Datum.IsCubicEmbedding` packages a closed immersion into relative projective
space which lies over the base and pulls back the degree-one twist to the
actual cubic bundle. Unlike `Datum.IsFrameEmbedding`, this condition neither
chooses a projective frame nor allows an extra twist by a base line bundle.
It does not assert existence of a cubic embedding.

`Datum.IsCubicEmbedding.hasGeometricFibreHilbertPolynomial` verifies the
section-rank test for the actual image ideal, in its fibre-product model.
The polynomial is `cubicHilbertPolynomial g d = 6^g d T^g`, with threshold
one on every geometric fibre. The proof identifies the kernel subscheme
with the source via the closed immersion's image comparison. Over an
algebraically closed test field, the projective twist pulls back to the
cubic bundle of the base-changed datum by the given twist isomorphism and
compatibility of the cubic bundle with base change. The recursive powers in
the Hilbert-family criterion are identified with the explicit tensor powers
and then with the actual cubic power bundles. The fibre section-rank
comparison and the cubic-power cohomology calculation give the value
`(6k)^g d` at each positive `k`.

`exists_boundedEquations_cubicEmbedding g d m` gives one cutoff for the
kernel ideal of each such embedding in polynomial projective space over
any commutative local ring in this universe, and in particular any field.
The cutoff does not depend on the level, prerequisites, ring, datum, or
embedding. The kernel subscheme is flat and locally of finite presentation
over the base because it is isomorphic to the abelian scheme over that
base. The fixed-polynomial cutoff therefore applies. Transport of the
kernel along the projective comparison isomorphisms identifies the ideal
with the actual kernel of the composite to polynomial projective space.

This is a derived application of the bounded-equation theorem on a fixed
Hilbert piece and of the cubic-power cohomology computation. The polynomial
and its normalization are those of Mumford–Fogarty–Kirwan, *Geometric
Invariant Theory*, 3rd ed., Chapter 7, printed p. 131 (PDF p. 144), as
explained in `FrameEmbeddingHilbertPolynomial.md`. The cohomological
transport here uses the exact twist isomorphism instead of trivializing a
base line on geometric fibres. The bound concerns generators on standard
charts of the ideal sheaf, not the degree of generators of a homogeneous
ideal in the polynomial ring. It does not assert determination from
labelled points.
