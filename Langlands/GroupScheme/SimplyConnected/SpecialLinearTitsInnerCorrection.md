# Inner correction preserving the diagonal split torus

Author: Worker 239.

This internal unit combines the actual all-test weight calculation,
blockwise matrix Hilbert 90, and the coordinate-change construction. It
starts from a local presentation `E : SL_(n+1) → G` over `Spec L`, a split
commutative group scheme `S` over a field `K`, a homomorphism `f : S → G`,
and characters `χ i` whose values give the diagonal coordinates of `S` in
`E` on every test scheme. The fields have arbitrary characteristic.

An inner discrepancy matrix has zero `(i,j)` entry whenever `χ i ≠ χ j`.
Indeed, the perfect character/cocharacter pairing of a split torus gives
one cocharacter separating this pair of characters, and the existing
Laurent-polynomial test gives the zero entry. The proof transfers the
perfect pairing along an actual split-torus isomorphism. No single
cocharacter separating all pairs is required.

Suppose `H` is a finite subgroup of the `K`-automorphisms of `L`, and a
supplied family `c σ ∈ GL_(n+1)(L)` represents its inner discrepancies and
satisfies `c 1 = 1` and `c (σ τ) = c σ · σ(c τ)`. Blockwise Hilbert 90, with
the characters themselves as labels, gives a matrix `P` with the same
zero pattern and `c σ = P · σ(P⁻¹)` for all `σ ∈ H`.
`innerCorrectionMatrix` is a noncanonical choice of such a `P`.
Its specification lemmas record this coboundary equation and the zero
entries between unequal character labels.

Every matrix of this block shape commutes with every actual torus
coordinate: entrywise, equal characters give equal diagonal values, and
unequal characters give zero entries. This remains true after every
coefficient homomorphism associated with a cover point. Consequently,
changing `E` by conjugation with the chosen `P` makes all discrepancies in
`H` the identity and preserves the original diagonal torus coordinates
on every test scheme.

The proof is derived from the imported weight-line, coordinate-change,
and block-descent results. The normalized inner cocycle is supplied;
its construction from distinguished end vertices is available separately
in `SpecialLinearTitsWeightLines`. This unit constructs no quadratic
field or Hermitian form and does not assert the final outer type A
presentation.
