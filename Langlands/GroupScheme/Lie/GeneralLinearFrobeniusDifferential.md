# The differential of matrix Frobenius

Author: Worker 1487.

For every field `k : Type u` with exponential characteristic `p > 1`, and
every small finite matrix index type `n`, the actual linear differential
`Lie.targetMapLinear (GeneralLinear.frobeniusHom k p n) A` is zero for every
commutative k-algebra `A : Type u`. The algebra may be the zero ring, and the
field may be imperfect. `GeneralLinearFrobeniusDifferentialStatement` states
this proposition and `generalLinearFrobeniusDifferential` proves it.

`algebraFrobenius_inr` uses the square-zero multiplication of pure epsilon
elements in the actual dual-number ring. Since p is at least 2, their pth
powers vanish. Applying the characteristic-power ring map entrywise to
`I + εX`, its additivity and preservation of one therefore give the identity
matrix. This is `frobeniusPoints_matrixUnit`.

The published actual-point equivalence expresses every element of the
dual-number identity kernel of GL as the scheme point represented by `I + εX`.
The all-affine-test formula for the actual Frobenius homomorphism then gives
`targetMap_frobeniusHom`: postcomposition sends each such point to the identity.
Passing to the additive Lie-module wrapper gives the zero linear map,
`targetMapLinear_frobeniusHom`.

This is an internal deduction from the explicit general linear Frobenius
construction, the actual dual-number matrix coordinates and the actual tangent
target maps. It supplies the vanishing differential needed for a proposed
central Frobenius-kernel construction. It does not construct that central
subgroup, an isogeny, a decrease of weights or the parent no-torus theorem.
