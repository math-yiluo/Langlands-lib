# Root-generated reflections for a finite Hermitian middle space

This internal continuation of `HermitianRootElimination` constructs an actual
root-generated reflection for an arbitrary finite diagonal Hermitian middle
space. It uses only the coordinate model and field algebra.

For a root parameter with vector `x` and nonzero scalar `z`, the two new
`Parameters` constructions have coordinates

    left:  (-x/bar(z), 1/bar(z)),
    right: (-x/z,      1/bar(z)).

Both satisfy the root trace equation. The implemented proofs factor the common
norm denominator out of the finite pairing sum and use
`z + bar(z) = Σ_i w_i*x_i*bar(x_i)`. The vector minus signs follow from this
model's positive middle entries in the opposite root matrix.

`reflectionElement` is the actual invertible product
`L(left) * U(x,z) * L(right)`, using the existing opposite and upper root
homomorphisms. Subgroup closure puts it in `elementarySubgroup H`; the
already proved containment then puts it in `specialUnitarySubgroup H`.
Thus the determinant-one and form-preservation assertions are inherited from
actual root factors.

`reflectionMiddle` is the matrix

    R_ij = delta_ij - bar(x_i)*w_j*x_j/z.

`reflectionMatrix` has the block form

    [ 0       0       z ]
    [ 0       R       0 ]
    [ 1/bar(z) 0      0 ].

`reflectionElement_val` proves that the three-factor product equals this
matrix. Its proof evaluates the nine kinds of block entries, factors the
finite sums, applies the root trace equation, and clears the two nonzero
denominators. This also covers an empty middle index and vanishing weights.
Although `reflectionMiddle` and `reflectionMatrix` are defined for every
parameter, the factorization and membership conclusions require `z≠0`.

The field universe and finite middle-index universe are independent. There is
no characteristic, nonidentity-involution, nondegeneracy or anisotropy
assumption. The result supplies concrete root-generated block reflections;
generation of the middle Levi, group-scheme comparisons and the unrestricted
local Kneser–Tits proposition remain separate obligations.
