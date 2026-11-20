# Normalization of the full elliptic Cartan window sum

`cartanWindowSum p x` sums over the complex and real slot permutations. Each complex
slot contributes the exponential of its radial parameter times the finite rotation
Fourier window. Each real slot contributes its `realTerm` factor.

The angular factor at angle `θ` is `expMode 1 θ - expMode (-1) θ`, which equals
`2 i sin θ`. Its product over the complex slots is nonzero when every complex
angle has nonzero sine. This product depends only on the Cartan coordinates.

The Lean proof distributes the angular product into the two permutation sums
and then into the complex-slot product. In each slot the existing finite-window
identity converts its contribution into the difference of the two `complexTerm`
orientations. Positivity identifies the absolute weight used to index the window
with the given integer weight. The real-slot factors are already the ones in
`numerator_apply`. Consequently a scalar multiplying the window sum becomes that
scalar divided by the angular product multiplying the numerator. This is an internal
finite consequence of the window and numerator formulas.
