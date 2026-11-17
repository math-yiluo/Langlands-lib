# The padded gauge integrand in block-root coordinates

This internal helper expresses the scalar part of a padded simple-root gauge
in the coordinates of `AdelicSimpleRootGaugeTorusCoordinates`. The ambient
root row is the row of the active block roots followed by coordinates equal
to one. Their product is the first diagonal idele. Combining this identity
with the determinant's weights shows that the negative gauge power and the
positive determinant power contribute the factor
`∏ j, |aⱼ|^((j + 1) * σ - τ)`.

`extendByOne` is continuous and, when the source has no more coordinates than
the target, a closed embedding. Its continuous left inverse is coordinate
restriction. These are finite-product topology statements.

The proof uses the previously established padded root formulas, maps finite
idele products through the idelic norm, and distributes real powers of
positive finite products. Its provenance is internal algebra and topology of
the Library's actual matrix and norm definitions. It proves no quotient
integration formula and no convergence estimate. The generic gauge definitions are imported from the Library.
