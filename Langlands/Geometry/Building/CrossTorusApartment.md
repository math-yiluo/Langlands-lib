# Actual valuation apartments under cross-torus isomorphisms

Author: Worker 118.

Over an arbitrary field, let `e : S ≅ S'` and `f : G ≅ H` be actual
commutative-group and ambient group-scheme isomorphisms whose square with the
inclusions `i` and `j` commutes. Assume both underlying inclusions are
monomorphisms and both ambient structural morphisms are affine. For supplied
`D : KPApartmentData i ω`, the constructor
`D.apartmentTransportAffineEquiv e f h` is an affine equivalence from the actual
valuation apartment `D.Apartment` to `(D.transport e f h).Apartment`.
The function `ω : kˣ → ℝ` is unchanged.

The underlying equivalence `D.apartmentTransportEquiv e f h` maps each point's
full valuation family by `RootFunctionFamily.transportEquiv e f`. Its inverse
uses the inverse of that same family equivalence; the carrier membership
formula for transported data supplies the inverse point's membership proof.
Point extensionality and the family inverse laws establish both inverse laws.
Consequently values at simultaneously transported actual characters and
ambient rational points are unchanged, including the infinite value.

The affine derivative is exactly `translationSpaceTransportEquiv e f h`,
the existing linear map on the quotients of the actual real cocharacter
spaces by their root annihilators. Quotient induction reduces compatibility
with the original point translations to the existing full-family translation
identity. This establishes the affine constructor and its displacement
formula without selecting an origin in either apartment.

The existing normalizer actions on points are intertwined through
`normalizerPointsTransportEquiv e f h`. Extensionality promotes this identity
to a commuting square of the original normalizer affine automorphisms.
At every point, for every character and every real level, the actual ambient
rational-point map preserves and reflects membership in the original
filtration subgroup. Its image is the entire target filtration subgroup
at the transported point and character, with exactly the same real level.
These last claims reuse the exact filtration-set image and membership
identities from `CrossTorusValuation` and `CrossTorusFunctions`.

The provenance is internal: this constructs points and an affine map from
the existing transported apartment data, valuation-family equivalence and
quotient translation equivalence, with their intrinsic identities. It
requires supplied apartment data. It asserts no existence of such data for
arbitrary groups and no comparison with independently chosen target data.
Full centralizer V6, topological V7, apartment intersections, full A2,
and general building existence remain separate obligations.
