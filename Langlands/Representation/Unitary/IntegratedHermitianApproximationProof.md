# Proof of continuous Hermitian integrated approximation

Worker 116 proves
`Langlands.Analysis.integratedHermitianApproximation` of exact type
`Langlands.Analysis.IntegratedHermitianApproximationStatement`, with
independent group and Hilbert-space universes. Worker 1276 adopts this
proof for the focused exact-target proof task, retaining its mathematical
content and Worker 116's authorship. It imports the unchanged public
target and the four prerequisite proof modules.

The proof derives norm preservation from the given complex inner product
identity. It invokes `hermitianWeightSequence` for the actual group,
measure and continuous multiplicative density, obtaining actual
continuous compactly supported nonnegative real weights. It separates
their integrability proofs and packages the remaining scalar properties
without changing the witnesses.

For each weight, its pointwise real Hermitian equation is coerced to ℂ.
Conjugation fixes real values, and the two coercions of the NNReal density
agree. Continuity makes that density measurable. Applying
`integratedUnitarySymmetry` with the actual inversion-density measure
identity yields symmetry of the literal integrated operator.

The constructor's `integratedIsometricAction_norm_le` bounds the operator
norm by the integral of the complex norm of the real weight. Pointwise
nonnegativity identifies this norm with the original real function;
normalization makes the integral one.

The ordinary support of each weight lies inside its topological support.
Thus the eventual topological-support inclusion supplies the
ordinary-support hypothesis of `integratedIsometricApproximation`.
That theorem gives strong convergence on every vector using the given
AE orbit measurability and identity continuity.

Finally, for every closed invariant P, the proof applies
`integratedIsometricNaturality` at each index. Classical choice collects
the preservation witnesses. The same theorem supplies the literal
ambient equation for each actual group-intertwining complex-linear
isometric equivalence P to Q and every operator index.

The proof assembles the preceding internal continuous Bochner results.
It proves no compactness, smoothness, concrete Haar/modular identity,
automorphic realization or spectral decomposition. The target Markdown
records the original Getz–Hahn motivation and these scope boundaries.
