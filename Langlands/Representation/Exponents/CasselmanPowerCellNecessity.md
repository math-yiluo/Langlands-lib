# Strict exponent bounds from supplied power-cell geometry

Author: Worker 1680.

This internal supporting unit separates the measure argument for strict
Jacquet exponent bounds from the remaining geometric existence results.
It uses the actual central quotient, the actual normalized Jacquet functor
and its actual inverse-half Haar-modulus character. Its proof generalizes
the geometric-series contradiction in the published
`ProductLeviSquareIntegrableExponent.lean`, using the generic countable-cell
Lp lower bound instead of that module's matrix-specific cells.
No disjointness, lower volume or Iwahori contraction existence is proved
for a reductive group here, and the full Casselman criterion remains open.

`powerDoubleCosetCell K g n` is the image of the actual double coset
`K g^n K` under the projection to the quotient by the full point center.
It is open: the double coset is the product of an arbitrary set with the
open subgroup on the right, and the quotient projection is open.

`HasGeometricPowerCellVolumes` requires these cells to be pairwise
disjoint and their measures to be at least `weight^n` times the measure
of the image of `K`, for every natural number `n`. These are explicit
geometric hypotheses on the actual sets and measure. In particular,
they exclude repetition of cells of positive measure.

`weighted_eigenvalue_lt_one_of_memLp_powerCells` starts with a vector
fixed by `K`, a functional invariant under `K`, a nonzero initial
coefficient and the exact coefficient law
`ℓ(ρ(g^n)x) = μ^n ℓ(x)`. The same coefficient law holds on `K g^n K`
by invariance on both sides. A unitary central character descends its
norm to the central quotient. The generic `countableCellLpLower`
theorem bounds the sum of squared coefficient lower bounds times cell
volumes by a finite number, because the coefficient is in L2.

The supplied volume bounds then make
`∑ n, (weight * ‖μ‖ₑ^2)^n * C` finite, where
`C = ‖ℓ(x)‖ₑ^2 * haar(image K)` is nonzero: Haar measure is positive on
the nonempty open image of `K`. If the ratio is at least one, the
geometric sum is infinite. This contradiction proves
`weight * ‖μ‖ₑ^2 < 1`.

`norm_lt_one_of_normalizedJacquet_exponent_of_powerCells` applies that
argument to the exact coefficient already constructed from a generalized
character of the actual normalized Jacquet representation pulled back
along a supplied homomorphism into the Levi. The chosen point is central
in the Levi; cofinal Iwahori contractions for this same point are supplied.
For every compact open subgroup, the required power-cell geometry is
assumed with weight equal to the squared extended norm of the actual
inverse-half Haar-modulus character. The coefficient eigenvalue is the
inverse of that character value times the normalized exponent value.
The two modulus factors cancel exactly, leaving the square of the
exponent norm below one and hence the strict norm bound.

The ambient group, character-domain and carrier universes are independent.
The original square-integrability predicate supplies representation
admissibility, its unitary central character and L2 integrability of the
smooth coefficient used. No global Jacquet admissibility,
irreducibility or finite-length premise is added. The additional cofinal
contraction and disjoint-cell lower-volume assumptions remain explicit
and have not been derived from the original represented-parabolic
Casselman hypotheses.
