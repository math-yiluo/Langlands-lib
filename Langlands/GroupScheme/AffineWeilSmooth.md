# Smoothness of the actual affine group-scheme Weil restriction

Let `A → B` be a finite projective homomorphism of commutative rings in an
arbitrary common universe. For an actual smooth affine group scheme `G` over
`B`, the previously constructed `AffineWeil.groupScheme A B G` is smooth over
`A`. Its actual coordinate algebra is the finite-type Weil restriction of the
global-section coordinate algebra of `G`.

First, `affineCoordinate_smooth_iff` identifies smoothness of an affine relative
scheme with smoothness of its actual global-section algebra over the specified
base ring. It compares the spectrum of the algebra structure map with the
original structure morphism using the canonical affine isomorphism. Smoothness
transfers in both directions through that isomorphism.

The coordinate algebra of `G` is therefore smooth, hence finitely presented.
`finitePresentationCoordinateEquiv` applies the existing representing-algebra
comparison to identify the actual finite-type restriction coordinates with the
finite-presentation restriction coordinates. The comparison sends the actual
universal tensor-valued point to the finite-presentation universal point.
The existing finite-projective Weil restriction smoothness theorem proves
smoothness of the latter algebra by infinitesimal lifting. Transport across the
algebra equivalence proves smoothness of the actual restriction coordinates.
Finally the spectrum criterion proves smoothness of the actual structure
morphism of `AffineWeil.groupScheme A B G`.

This is an internal assembly of the existing finite-type/finitely-presented
comparison, the canonical affine isomorphism, and the established Weil
restriction infinitesimal lifting proof in
`Langlands.TauCeti.RingTheory.WeilRestriction.Smooth`.
It changes neither the original group scheme nor the restriction construction.
It proves smoothness only. Connectedness, geometric reductivity, finite separable
splitting and the local Kneser–Tits theorem remain separate obligations.
