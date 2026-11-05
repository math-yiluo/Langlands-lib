# Levi-compatible Iwasawa conclusions from diagonal star realization

Author: Worker 1655.

This internal construction combines the existing affine polar compact
construction, diagonal dynamic parabolic covering, and the actual unitary
intersection results. It works over an arbitrary-universe `RCLike` field
`𝕜`, on actual affine points over `𝕜` with their regular-function evaluation
topologies. The ambient group scheme is affine.

`HasDiagonalStarLeviRealization p m` is a Prop-valued existence predicate.
It asks for a finite closed matrix representation, a cocharacter and integer
weights satisfying `IsDiagonalLeviPair`, and stability of the representation's
actual rational-point range under conjugate transpose. The morphisms `p`
and `m` are the specified actual parabolic and Levi maps into the ambient
group. Their representation as dynamic subgroups is an assumption of this
predicate; no existence theorem for such data is asserted here.

Given these data, the constructed compact subgroup is the actual inverse
image of the standard unitary matrix subgroup. The affine polar construction
proves its compactness and maximality among every compact overgroup.
It also constructs, for each ambient point, a unitary right factor with
positive definite represented remainder. A positive definite matrix is
Hermitian, so the existing diagonal dynamic covering theorem gives the
literal ordered product `range p * K = Set.univ`. There is no supplied
compact subgroup, factorization or covering premise in this construction.

The previously proved unitary intersection identity gives
`range p ∩ K = range m ∩ K`. This is an equality of actual point ranges,
without replacing them by closures or abstract models.

For the final maximality conclusion, representation of the dynamic
centralizer implies that `m` is a closed immersion. Its source is therefore
affine, and restricting the original closed representation along `m`
gives a closed representation of that source. The unitary intersection
module passes ambient conjugate-transpose stability to this restricted
representation by extracting actual Levi preimages. Applying the affine
polar construction again proves compactness and unrestricted maximality
for its unitary inverse image. This is definitionally the comap of the
ambient unitary inverse image under the actual point homomorphism induced
by `m`. Both compactness assertions use the evaluation topology of their
own point carrier.

`HasDiagonalStarLeviRealization.hasLeviCompatibleDecomposition` packages
the constructed witness using the existing generic four-conclusion
predicate. The result is conditional on realization data. Constructing
such data from the rational parabolic and supplied rational Levi, and
performing the required archimedean scalar and completion comparisons,
remain obligations for the unchanged full
`InfinitePlaceGroupPoints.LeviCompatibleIwasawaStatement`.
