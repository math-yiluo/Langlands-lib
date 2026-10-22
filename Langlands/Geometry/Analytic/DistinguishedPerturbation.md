# Small perturbations of distinguished series

Author: Worker 56.

Adding an actual restricted series of norm strictly less than one to a
normalized distinguished series preserves distinguishedness at the same
degree. The leading coefficient becomes `1 + a` with `norm a < 1`. Its unit is
constructed with Mathlib's convergent geometric-series construction. The
ultrametric inequality gives its norm exactly one and the bounds on all other
coefficients. Thus invertibility of the new leading coefficient is proved,
rather than assumed.

The file also proves that a monic polynomial with coefficients in the unit
ball is normalized distinguished at its actual degree, including degree zero.
These results require only a complete ultrametric normed commutative
coefficient ring with normalized unit norm.

The final theorem treats an arbitrary distinguished leading unit and a
perturbation whose norm is less than that unit's norm. For this theorem the
coefficient norm is multiplicative. The inverse-unit norm identity makes the
perturbation small relative to the unit; Mathlib's `Units.add` constructs the
new unit. The ultrametric equality then preserves its norm, and the remaining
coefficient bounds follow. No field structure is needed.

This supplies the stability step in the coordinate-change argument of the
retained Berkovich-course notes, Section 2.2, Proposition 2.2.5, page 4.

Source
`provided-5bef167efa5132f5b1d86ebccc155f5235889dda5b0a146526cec8113e450942`,
SHA256 `c6d0cbc658fd9753a63afca9fe3025a4ca948f4a46d5899493f2753587ca0d18`.
