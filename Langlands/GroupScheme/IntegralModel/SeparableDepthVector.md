# Polynomial models of actual separable additive depth lattices

Let `K` have a surjective integer-valued valuation with Henselian valuation
ring, and let `L/K` be finite and separable. Fix a `K`-basis of `L`.
For every real depth `r`, `separableDepthVector` is a smooth affine integral
model with geometrically connected fibres and a fixed generic polynomial
vector group of dimension `[L : K]`.

Its generic identification uses the actual depth-lattice integral basis
constructed in `HenselianSeparableDepthBasis`, expressed in the fixed
reference basis. Interpreting rational vector coordinates in `L` through
that reference basis identifies its integral-point image exactly with
`henselianSeparableDepthLattice v hH L r`, the actual valuation-depth ball.
No unramifiedness of `L/K` is assumed.

For `r ≤ s`, the actual inclusion of the depth `s` lattice in the depth
`r` lattice has integral coefficient matrix
`separableDepthTransitionMatrix`. Rationalizing this matrix gives the
change matrix between the two field bases. Consequently it defines an
integral-model map extending the generic identity. Every map extending that
same generic identity has smooth, connected, unipotent scheme-theoretic
kernel on special fibres. This follows from the general basis-matrix model
and its actual matrix-kernel theorem, using generic rigidity for the
arbitrary supplied extension.

This is a derived polynomial presentation of the additive depth-lattice
construction supporting Kaletha–Prasad, *Bruhat–Tits theory: a new approach*
(2023), Section C.2, printed pp.697–698 (PDF pp.728–729). The extension field
may have an independent universe level. This file interprets rational
points in `L`; it does not construct an all-test comparison with a separately
supplied Weil restriction, an actual relative root subgroup, or a supplied
apartment filtration. Those comparisons and the full C.5.3 target remain
separate obligations.
