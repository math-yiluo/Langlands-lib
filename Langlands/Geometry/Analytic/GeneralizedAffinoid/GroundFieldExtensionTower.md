# Direct and successive ground field extension of affinoid algebras

Let `K → L → M` be a tower of ultrametric normed fields, in independent
universes. Each of the three algebra maps is the structural map of a normed
algebra, and `IsScalarTower K L M` identifies the composite with the direct
map. Let `A` be any presented `K`-affinoid algebra. Write `A_T` for the
Library's `GroundFieldExtension.algebra K T A`, the quotient of the weighted
Tate algebra over `T` at the original arity and radii by the closed ideal of
extended relations. This notation denotes the actual quotient, not an
arbitrary isomorphic algebra.

## The comparison

When `M` is complete, `towerEquiv K L M A` is a bounded `M`-algebra equivalence
from `(A_L)_M` to `A_M`. To construct the forward map, regard `A_M` over `L`
by restriction of scalars. Lift `ι : A → A_M` first to an `L`-algebra map out
of `A_L` and then to an `M`-algebra map out of `(A_L)_M`. For the reverse map,
regard `(A_L)_M` over `K` by restriction of scalars and lift the composite
`A → A_L → (A_L)_M` directly to an `M`-algebra map. The original field tower
ensures that the restricted scalar structures agree along the intermediate
field. The lift formulas identify corresponding presentation coordinates in
both directions, so extensionality on those coordinates makes both
composites identities. The packaging retains the two bounds.

`towerEquiv_iota` states, for every `a : A`, that the double structural image
of `a` goes to its direct structural image. This equation is obtained from the
two lift equations, not just from the comparison of spectra.
`towerEquiv_coordinate` records the corresponding equation for presentation
coordinates. If `L` is also complete, `towerEquiv_naturality` compares the
actual bounded maps obtained by extending any bounded `K`-algebra map
`f : A → B` directly or successively. Both routes send each presentation
coordinate, under `f` and the structural maps, to the same element of `B_M`.

## Spectra and scope

`towerSpectrumHomeomorph` is the contravariant homeomorphism from the
spectrum of `A_M` to the spectrum of `(A_L)_M`. It acts by evaluation along
`towerEquiv`, as made explicit in `towerSpectrumHomeomorph_apply`. The two
projections to the spectrum of `A` agree by `towerEquiv_iota`; the spectrum
homeomorphism is natural by `towerEquiv_naturality`. Neither `K` nor `L`
needs to be complete for the equivalence or the projection identity.
Completeness of `L` is used for the functorial maps in the naturality
identities. There is no strictness, degree, nonzero quotient or nontrivial
valuation assumption.

## Provenance

Conrad–Temkin, *Non-archimedean analytification of algebraic spaces*,
24 February 2009 preprint, Theorem 2.3.5, printed and PDF p. 13, states the
transitivity of the natural analytification comparisons under further
extension of the ground field. The construction here is the affinoid-algebra
input for comparing direct and successive analytic extensions in that
transitivity statement. It is derived using the Library's bounded lift
universal property of the presented ground field extension; the source does
not formulate this particular quotient-presentation comparison. This module
does not assert the glued atlas comparison, the compatibility with fibre
products, or the transitivity square with analytification.
