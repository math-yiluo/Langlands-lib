# The opposite-algebra similitudes and translations in Harris's Appendix

The module works over a commutative scalar ring `k` and a `k`-algebra
`B`. In Harris's split local group, `k` is `ℚp` and the scalar map
factors through the center of the division algebra `B` over `F`.
`splitInvolution` exchanges the factors of `Bᵒᵖ × B`, using the
opposite algebra to reverse multiplication. The resulting
`AlgebraInvolution.similitudes` is the actual group of a unit of the
product algebra together with its scalar multiplier.

`splitSimilitudeCoordinates` uses the Library's central-idempotent
splitting for the first factor. A similitude is determined by its
opposite component `d` and multiplier `e`. The reconstructed second
component is `e` times the inverse of `d` in the original algebra.
The code proves the equation `d d' = e` in that algebra, with the
scalar embedded by the given algebra map.

`weilComponentElement` has first component `Π` and multiplier `p^f`.
Right multiplication changes a pair to
`(d Π, d' p^f Π⁻¹)`. `determinantComponentElement` has first component
`Π^(-detOrder)` and multiplier one. Its right multiplication is
`(d Π^(-detOrder), d' Π^detOrder)`. In each formula the first product
is in the opposite algebra. The right translation signs are the
component formulas for the Weil operator and the general linear
action in Harris 1997, Appendix, (A.3) and (A.6).

These are identities on the actual split similitude pairs before
the quotient by the compact subgroup. The component quotient,
its identification with valuations, and the action on the formal
moduli functor require further constructions.

The source is Harris, *Supercuspidal representations in the
cohomology of Drinfel'd upper half spaces* (1997), Appendix,
printed pp. 112–114 (PDF pages 38–40), including (A.2) and (A.3),
and (A.6), printed p. 115 (PDF page 41).
