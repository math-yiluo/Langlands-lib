# Geometric vector coordinates and unipotence of commutative p-torsion groups

This internal construction combines the published algebraically closed
classification in `Rational.CommutativePTorsionVectorProof`, geometric
connectedness of finite type group schemes in `GeometricConnectedness`, and
unipotence reflection in `Unipotent.FieldReflectionProof`. It supplies the
representation-theoretic comparison needed for the complement in the
vector-factor decomposition of CGP B.2.5.

`HasUniformPowerExponent.baseChange` transports the all-test exponent along any
base morphism using the multiplicative pullback adjunction on points.
`HasUniformPowerExponent.of_iso` transports it along an actual group-scheme
isomorphism by cancellation. Neither requires reduced scheme tests.

For a field `k` of prime characteristic `p` and a smooth connected commutative
affine group scheme `G` killed by `p` on every relative scheme test,
`CommutativePTorsion.isVectorGroup_algebraicClosure` proves that its actual base
change to `AlgebraicClosure k` is a vector group. Smoothness and affineness
persist under pullback. Connectedness persists by
`connectedSpace_baseChange_of_smooth_affine`. The transported all-test exponent
then permits application of `RelativeRoot.smoothCommutativePTorsionVector`.

`geometricVectorDimension` chooses the finite dimension supplied by that
classification, `geometricVectorDimension_spec` retains the natural all-test
coordinates, and `geometricVectorIso` is the resulting actual group-scheme
isomorphism to the standard vector group. The dimension may be zero.

Finally, `CommutativePTorsion.isUnipotent` uses
`RelativeRoot.IsVectorGroup.isUnipotent` over the algebraic closure and
`IsUnipotent.of_baseChange` to obtain the existing coefficient-representation
predicate over `k`. No perfectness, infinitude, embedding, or ground-field vector
classification hypothesis is added. The construction does not claim that `G`
is a vector group over an imperfect ground field, and does not yet construct the
ground-field vector factor or a wound complement.
