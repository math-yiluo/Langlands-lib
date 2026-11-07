# Characteristic-power congruence on actual group points

This is derived content. It uses the published actual affine evaluation
laws, the characteristic-power ring homomorphism, and the intrinsic
origin condition from `FrobeniusCovariantInvariants`. No new external
source assertion is used.

Let `G` be an affine group scheme over a field `k : Type u`, let `p` be
its exponential characteristic, and let `r` be any natural number.
For every relative scheme `V`, `Congruent G p r V g h` says that the
values at `g` and `h` of every actual affine coordinate have equal
`p^r`-th powers in the global sections of `V`. The relation is reflexive,
symmetric and transitive. It is preserved by multiplication in both
arguments and by inversion. Multiplication follows from actual
coordinate comultiplication: the characteristic-power map is a ring
homomorphism, and tensor induction reduces the comparison to products
of coordinate values. Inversion uses the actual coordinate antipode.

The Hopf/Lie coordinate equivalence detects exactly the same congruence.
The value of any Lie coordinate at the actual identity is its
`coordinateOrigin` embedded in the global sections of `V`. Subtracting
that constant coordinate and applying the characteristic-power ring map
therefore proves `isOriginTestPoint_iff_congruent_one`: the intrinsic
Frobenius-origin condition is precisely congruence to the identity.
The converse also uses that `p^r` is nonzero, which follows from
exponential characteristic.

`originTestSubgroup` has exactly those intrinsic origin points as its
carrier. The preceding operation laws give its subgroup structure.
It is normal, since multiplying a congruence to the identity on the
left by `g` and on the right by `g⁻¹` gives another congruence to the
identity. Two congruent points `g` and `h` differ by the origin point
`g⁻¹ * h`. Consequently `pointAlgebraHom_eq_of_congruent` proves that a
coordinate invariant under right multiplication by every intrinsic
origin point has equal evaluations on any congruent pair.

All these statements retain arbitrary relative test schemes, including
nonaffine, nonreduced and empty tests. Height zero, exponential
characteristic one and the trivial group are allowed. No smoothness,
connectedness, reductivity, torus or finite-dimensionality hypothesis
is used. This unit does not characterize invariant functions as
polynomials in characteristic powers, exclude the entire-covariant
kernel vector, or prove fixed-height restriction injectivity, the sharp
whole-space Steinberg dimension bound, or `SteinbergBigCellStatement`.
