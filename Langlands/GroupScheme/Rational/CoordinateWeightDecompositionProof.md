# Actual coordinate, augmentation and cotangent weight decompositions

`CoordinateWeights.coordinateWeightDecomposition` proves the exact Library
proposition `CoordinateWeights.CoordinateWeightDecompositionStatement` at every
universe `u`. For any field `k`, any affine group scheme `G`, any split torus `S`
and actual automorphic action `b` of `S` on `G`, it proves that the actual
coordinate, augmentation and cotangent character spaces are internal direct
sums. It also proves that the augmentation quotient maps each character space
onto the cotangent space of that same character. There are no characteristic,
smoothness, connectedness, reducedness or finite-dimensionality restrictions.
The augmentation and cotangent refer to the actual identity augmentation and
its quotient by its square, with the existing all-algebra eigenconditions and
direct pullback convention.

The proof applies `coordinateWeightDecompositionStatement_of_pointed` from
`CoordinateWeightPointedReduction`. Its first input is the published theorem
`PointedCoordinateWeights.pointedCoordinateDecomposition`, applied to the
underlying pointed scheme of `G`, whose fixed point is the identity. This gives
the coordinate and augmentation decompositions. Splitness makes `S` affine, so
`cotangentWeightSpace_iSupIndep` from `CoordinateCotangentIndependence` gives
independence of the actual cotangent weight spaces. That helper uses linear
functionals separating rational-character units, the universal point of `S`,
and the tensor-cotangent base-change equivalence to extract each term from a
finite relation. The published lemma `cotangentMk_mem_weightSpace` proves that
the quotient preserves each character.

The quotient is surjective. The images of the augmentation weight spaces thus
span the cotangent space and lie termwise in its independent weight spaces.
The modular-law transfer lemma in `CoordinateWeightPointedReduction` identifies
them termwise. It yields both cotangent internality and same-character lifting,
with no decomposition premise added to the target.

Provenance: this is a derived proof of the published actual-coordinate statement.
Its source context is Conrad–Gabber–Prasad, *Pseudo-reductive Groups*, second
edition (2015), §3.3, printed pp.107–108 (PDF pp.133–134), especially the
augmentation and direct pullback convention on p.107 and the quotient-weight
lifting in Example 3.3.2 on p.108. The implementation follows the pointed
coaction proof and the modular-law quotient argument described above. It uses
neither semigroup realization nor any commutator conclusion.
