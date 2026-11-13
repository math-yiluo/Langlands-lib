# Coordinate transport for special-linear diagonal weights

This internal helper relates the diagonal-entry characters to integral character
coordinates and supplies factor renaming for split tori. It is a conditional
coordinate adapter for the special-linear Tits-cocycle proof; it does not
construct a pinning or prove the full classification statement.

For any base scheme and finite factor sets `I` and `J`, an equivalence `e : I ≃ J`
gives `splitTorus.reindexIso` and `splitTorus.commReindexIso`, actual isomorphisms
of group schemes and commutative group schemes. On every relative test scheme
their forward maps send a family of units `t` to `j ↦ t (e.symm j)`. The proof
constructs this multiplicative point equivalence, checks naturality under
pullback of global sections and applies the published representability
construction `isoOfPoints`.

The projection-character formula follows by evaluating on every test scheme.
Over an arbitrary field, `commReindexIso_hom_comp_character` says that pulling
back the character with integral exponent vector `m : J → ℤ` gives exponent
vector `i ↦ m (e i)`. The proof expands the character into its finite sum of
coordinate projections, uses the projection formula and reindexes that sum.

For any finite matrix index type with a chosen pivot, the character
`SpecialLinear.diagonalWeight` is the inverse image under the published
split-torus character equivalence of the vector `c ↦ weightCoord p i c.down`.
Consequently `GeneralLinear.characterCoordEquiv` sends this character to
`weightCoord p i`, and a difference of diagonal weights is the inverse image of
the difference of those vectors. These results follow directly from the finite
sum defining `diagonalWeight` and the inverse formula for the character
equivalence. They impose no positive-rank or characteristic restriction.

All content is derived from the published split-torus point and character
constructions and the diagonal-weight helper. There is no additional
literature claim or classification premise.
