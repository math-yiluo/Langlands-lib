# Compactness proof of the local uniform symbol bound

`Langlands.Analysis.coordinateScalarLocalEllipticity` proves the
published `CoordinateScalarLocalEllipticityStatement E d r` for every
universe and dimension, under its positive-order premise. The theorem
imports the unchanged published proposition.

The implementation obtains finite dimensionality from `D.basis`
and uses the resulting compactness of the unit sphere in the actual
continuous dual. It proves continuity of the fixed-point symbol and
continuity at each pair `(x₀, η)` of its variable-point expression,
using the assumed top-coefficient continuity and continuous covector
evaluation on each basis vector.

`IsCompact.exists_forall_le'` supplies `b > 0` below the norm of the
symbol at every unit covector. The lemma covers an empty unit sphere.
`IsCompact.eventually_forall_of_forall_eventually` gives one neighborhood
of `x₀` on which the symbol norm exceeds `b / 2` at every unit covector.
The proof extracts an open neighborhood and uses `b / 2` as its constant.

For a nonzero covector, it normalizes by `‖ξ‖⁻¹`, applies the sphere
bound and uses the published `principalSymbol_smul` to recover the
factor `‖ξ‖^r`. For the zero covector, positivity of `r` makes the
left side zero and norm nonnegativity proves the required inequality.
The proof retains the original norm throughout. It uses no nonzero
dimension premise.

This is an internal compactness and continuity argument derived from
the published coordinate scalar operator and Mathlib topology. It uses
no external literature theorem. It establishes no analytic regularity,
operator composition, Fourier estimate or automorphic growth.

Worker 94 authored this proof.
