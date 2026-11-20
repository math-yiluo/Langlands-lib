# Matrix realization of the elliptic Cartan coordinates

`cartanElement` realizes a tuple in `Coordinates r s` as an element of `GL_n(ℝ)` for
`2 * r + s = n`. The first `2 * r` coordinates consist of consecutive complex planes, and
the last `s` coordinates are real lines. A complex slot with log radius `a` and angle `θ`
has the block `exp(a)` times the rotation with first column `(cos θ, sin θ)`. A real slot
with log radius `a` and sign exponent `z` has the entry `exp(a) * (-1)^z`.

The Lean construction uses a sigma type of block coordinates and transports the block diagonal
matrices to `Fin n`. The element is the product of the diagonal of positive radii and the
orthogonal matrix of rotations and signs. Their inverses are the diagonal of reciprocal radii
and the transpose, respectively. The transposed block products use orthogonality of the angular
and sign factors and reduce to a scalar diagonal in each block. Both Gram matrices therefore
have the diagonal `exp(2 * a)` at every coordinate of the slot with log radius `a`.

The coordinate label is surjective and the fiber over a slot is equivalent to `Fin 2` for a
complex slot or `Fin 1` for a real slot. Hence the number of `PairBlock` labels is `r`.
Distinct log radii give distinct squared radii. The off-diagonal entries within a plane are
opposite and are nonzero when its sine is nonzero. All cross-block entries are zero.
`realStandardEllipticCartanMatrix` collects these source hypotheses for the compact-column
support theorem. They are internal finite matrix and coordinate calculations.
