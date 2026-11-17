# Actual affine translation quotients

This is an internal geometric transport used in the construction of the quotient
by a closed diagonalizable subgroup, following the strong-grading construction
of SGA 3, Exposé VIII, §§4–5, especially Theorem 5.1. It applies over any
commutative ring `R`, to any abelian character group `M`, any group scheme `G`
over `Spec R` with affine underlying scheme, and a homomorphism
`i : D_R(M) → G`. Finite generation, smoothness and reducedness are not assumed.

`translationAction i` is the actual morphism `(d,g) ↦ i(d)g` on the product of
the two group schemes over `Spec R`. `translationProjection i` is the morphism
from `G` to the spectrum of its actual degree-zero coordinate algebra, obtained
using the canonical affine-coordinate isomorphism. These are constructions,
not supplied quotient data.

When `i` is a closed subgroup inclusion,
`translationProjection_isPullback` identifies `(d,g) ↦ (g,i(d)g)` with the fiber
relation of the projection. The proof transports the spectrum pullback of
`AffineDiagonalizableQuotient` through the actual product and coordinate
isomorphisms. `translationProjection_flat_surjective` transports the faithful
flatness of the degree-zero coordinate inclusion to this scheme projection.

For every relative scheme test `T` and morphisms `g,h : T → G`,
`translationProjection_left_fibers` proves that their images agree if and only
if `h * g⁻¹` lies in the range of `i` on `T`. In the forward direction the
pullback universal property produces a point of the subgroup; in the reverse
direction this point and `g` define a product point, and the pullback square's
commutativity gives equality of images. If the range is normal,
`translationProjection_fibers` conjugates this criterion to the standard
`g⁻¹ * h` criterion required by `NormalQuotientGroup`. These statements quantify
over all relative scheme tests, not only affine or field tests.

This module does not prove local finite presentation of the projection or
construct its descended group structure. Its provenance is derived: it
transports the preceding algebraic construction to the actual group schemes
and proves the explicit pointwise consequences of the resulting pullback.
