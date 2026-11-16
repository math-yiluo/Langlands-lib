# Principal-series transport by signed real reversal

This internal helper uses the signed involution of `RealMixedSwapTwist`.
The character list transforms by `χ'_j(x) = χ_(2-j)(x⁻¹)`, for the three
positions `j : Fin 3`. The pullback carries the smooth real principal
series of `χ` to that of `χ'`, and carries their orthogonal finite parts
in the same direction.

The implemented proof first conjugates the inverted transposes of diagonal
and upper unipotent matrices by the signed reversal. This inverts and reverses
the diagonal entries and preserves upper unipotence. Reindexing the product
in the normalized principal-series character by `Fin.rev` also reverses
the modulus exponents; inversion changes their signs back. Smoothness and
orthogonal finiteness follow from the previously proved pullback results.

Provenance: internal algebraic transport, based on the corresponding
published `ComplexReverseTwist` principal-series computation. All properties
are proved in Lean; no irreducibility or block swap is assumed.
