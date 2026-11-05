# Tensor-unit coordinates for Weil-restriction norms

Author: Worker 1587.

This internal interface specializes the existing corepresented affine-point model to
`WeilGm.groupScheme`. It is derived from the published constructions, rather than a
new assertion from the literature.

`affineUnitsEquiv` identifies the points on an affine test algebra `R` with the units
of `B ⊗[A] R`. Its naturality theorem identifies coefficient change with the map on
the right tensor factor.

For a field `k`, `rationalUnitsEquiv` removes the tensor factor `k` and identifies
ground-field rational points with `Bˣ`. `extensionUnitsEquiv` identifies rational
points of the actual base change to a field `L` with `(B ⊗[k] L)ˣ`. Extension of
ground-field points is tensor inclusion, and Galois conjugation acts on the right
factor.

For finite Galois `L/k`, `rationalNorm_tensor` expresses the existing descended
rational norm, after tensor inclusion, as the product of these coefficient
conjugates. The proof transports `rationalExtend_norm` through the multiplicative
point equivalence. This does not assert norm surjectivity or any boundedness
comparison.
