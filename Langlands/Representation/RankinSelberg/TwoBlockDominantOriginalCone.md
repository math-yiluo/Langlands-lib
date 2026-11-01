# Original-torus opposite support for the actual dominant product

This internal derived module combines the actual two endpoint estimates and
actual scalar-section internal-root support. It supplies a support step for the
JPSS (1983), Section 4.10(2) dominant-matrix argument (printed pp.419–420).
JPSS does not separately state this integer-lattice auxiliary formulation.

`IsTorusBlockSupport` gives a single natural cutoff before every original torus
exponent, right integral factor and both rectangles, on simultaneous nonvanishing
of the actual ambient coefficient and the actual oppositely twisted scalar
section. Every first-block exponent is bounded above by the cutoff and every
second-block exponent is bounded below by its negative. The bound may depend on
the coefficient, section and real twist; only smoothness of the ambient and
block representations is required. Zero functionals and arbitrary block sizes
remain allowed.

`exists_torus_block_support` converts the normalized absolute-value estimate
for the initial entry of the inverse first block and the terminal entry of the
second block into integer cutoffs, using the canonical uniformizer formula and
strictly increasing residue-cardinality powers. The scalar section supplies
an adjacent root bound inside both original blocks. Propagating it from each
endpoint gives the claimed cutoffs for every coordinate.

`oppositeCone_rotated_of_block_bounds` transports these two original-block
cutoffs through the exact block-rotation permutation. The second original block
occupies the initial interval in standard coordinates. The final theorem applies
this transport to the actual inverse-rotated torus representative, absorbing the
inverse block rotation into the right integral factor. The result is the existing
`OppositeCone` predicate used by geometric summability.

This module does not assert a rectangle-volume bound or analytic convergence.
The field, ambient test space and block representation universes are independent.
