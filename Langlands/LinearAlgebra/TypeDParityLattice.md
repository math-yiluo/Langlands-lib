# The integral type D parity lattice

This is an internal integer linear algebra calculation for the spin-kernel proof.
For a finite index type `l` with at least two elements, `pairLattice l` is the
integer span of `e_a + e_b` and `e_a - e_b` for distinct indices.
`sumParity l` takes the sum of the coordinates in `ZMod 2`.

The two kinds of generators have even coordinate sum. Conversely, choose an
index `a`. The difference between a vector `x` and its coordinate sum times
`e_a` is a sum of coordinate differences. Also `2e_a` is the sum of
`e_a + e_b` and `e_a - e_b`, for any `b` distinct from `a`. Thus every vector
with even coordinate sum lies in `pairLattice l`.

`pairLattice_eq_ker_sumParity` and `mem_pairLattice_iff` express this equality.
The parity map is surjective, since the single coordinate vector with integer
coordinate `val(z)` maps to each `z : ZMod 2`. The linear first isomorphism
theorem therefore constructs `quotientEquiv`, and `card_quotient` gives cardinality
two.

The provenance is the explicit calculation above, using only Mathlib's integer
modules, finite sums, `ZMod`, and the linear first isomorphism theorem. The file
does not identify this lattice with the coroot lattice of any particular
group scheme; that comparison is a separate step.
