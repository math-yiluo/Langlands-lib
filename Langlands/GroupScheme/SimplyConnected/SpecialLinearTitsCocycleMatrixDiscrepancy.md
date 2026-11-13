# Matrix evaluation of the actual Galois discrepancy

This internal helper identifies the Galois discrepancy of an actual
base-change isomorphism with its automorphism of the special-linear model
over the extension field. It uses the published cover-point and
special-linear model comparisons, together with the categorical discrepancy
construction of Worker 243.

`matrixDiscrepancyIso E σ` transports `GaloisDiscrepancy.groupIso E σ`
through `SpecialLinear.baseChangeModelIso`. It is an actual automorphism
of the special-linear group scheme over the extension field.
`matrixDiscrepancyIso_square` records the intertwining square for those
two automorphisms.

`scalarMap_coverTest` identifies the structure-ring homomorphism of the
induced test over the extension with `coefficients a`.
`discrepancy_eq_groupIso` applies the actual Galois pullback formula for
`LocalGroupIso.ofBaseChangeIso`, then composes with the original inverse.
`discrepancy_eq_matrixDiscrepancyIso` uses preservation of all matrix entries
by the special-linear model comparison and cancels that comparison with its
inverse. The result holds for every relative test scheme and cover point.
The cancellation is first proved for arbitrary categorical isomorphisms,
then projected to points of group schemes. A private comparison lemma
handles any automorphism of the base-changed special-linear group; the
final result composes it with `discrepancy_eq_groupIso`. An explicit equality
unfolds `matrixDiscrepancyIso` before that composition, keeping the final
kernel comparison small.

The fields, characteristics, universe and rank are unrestricted. No
finite-degree or Galois-extension assumption is required. This is a direct
composition of the actual categorical and point-comparison interfaces; it
does not assert a matrix classification or identify a based root action.
