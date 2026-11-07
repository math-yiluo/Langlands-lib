# Coefficient conjugation of actual normalizing opposite pairs

This internal unit concerns an actual group scheme over a field, a supplied
homomorphism from an actual commutative group scheme over the same field, and
an arbitrary field extension. It proves transport for the existing rational
point automorphism `GaloisPointComparison.rationalConjugate`. No Galois,
finite-degree, splitness, or reductivity hypothesis is needed for the transport
itself.

The module reuses `NormalizerGaloisAction` for
`IsNormalizingPoint.baseChangeBasePoint`, `IsNormalizingPoint.baseChange_descent`,
`rationalConjugate_eq_baseChange_descent` and
`rationalConjugate_mem_normalizerPoints`. These preserve the specified point and
the pulled-back acting-group automorphism through canonical descent. The
coefficient comparison identifies this pullback-and-descent point with the
existing rational coefficient conjugation. The new general-scheme corollary
`mem_normalizerPoints_descentBaseChange` forgets the automorphism witness.

`RelativeRoot.IsOppositeFactorPair.rationalConjugate` applies the published
all-test root-subgroup transport to each ordered negative-root factor. The
character is carried by the ordinary character-lattice Galois representation;
its negation transports by additivity. Multiplicativity and the proved
normalizer preservation show that the transported triple normalizes the same
descended torus. The middle point and both opposite points are the actual
coefficient-conjugate points, with their order preserved.

`RelativeRoot.oppositeFactorPairsGaloisMap` packages this theorem as a map
between the complete types of certified ordered opposite pairs. Its underlying
pair consists exactly of the two coefficient-conjugate factors, as recorded by
`oppositeFactorPairsGaloisMap_val`; it makes no new choice of points.

The provenance is an internal deduction from the existing actual pullback,
descent, inner-automorphism and root-subgroup transport results. It asserts no
new original-literature theorem. All fields and the universe remain arbitrary.
Existence of compatible split pinnings and normalized root coordinates, and
their transport laws, remain separate obligations. This transport result
does not prove the parent Steinberg quotient theorem or its geometric and
rational-lifting prerequisites.
