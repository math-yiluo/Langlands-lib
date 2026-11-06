# Levi projections on the target geometric-lemma intersection

This is an internal construction derived from the published represented
geometric-lemma intersection datum and its literal rational-point intersections.
It requires no additional structural hypothesis on the two parabolics.

Write \(P=MN\) and \(Q=LU\) for the original rational-point groups and fix the
datum's representative \(z\). The target intersection parabolic is
\(L\cap z^{-1}Pz\); its Levi is \(L\cap z^{-1}Mz\) and its radical is
\(L\cap z^{-1}Nz\). The map `targetParabolicPointsToStabilizer` includes this
parabolic in the orbit stabilizer for the representative \(z^{-1}\).
Composing with the stabilizer-to-inducing map gives literal conjugation by
\(z\), as recorded by `targetParabolicPointsToSource_apply_coe`.

The main comparison `targetParabolicPointsToSourceLevi_eq` says that conjugating
and projecting to \(M\) gives the same result as projecting to the intersection
Levi and conjugating. Its proof uses the unique-factorization characterization
of each semidirect Levi projection: the quotient of an element by its projected
Levi factor belongs to the intersection radical, so its conjugate belongs to
\(N\). Injectivity of conjugation then identifies the kernel with the target
intersection radical.

For an affine ambient group in its canonical rational-point topology, the
inclusion is continuous. The two conjugation maps are continuous when the
ambient rational-point group is topological, as is already assumed in the
local comparison target. The common-Levi map agrees with the datum's represented
conjugation homeomorphism, transported through the published point-image
identifications.

This construction treats the target intersection inside \(L\). The full
stabilizer decomposition, quotient integration, and comparison of the distinct
radical modulus characters remain separate obligations for the normalized
orbit comparison. No assertion of that final comparison is made here.
