# Intrinsic all-parabolic GL cusp functions in the original cuspidal space

Let `F` be any number field, in arbitrary universe, and let `n` be any natural
number. The source is the existing
`normalizedParabolicCuspidalSubrepresentation` of actual continuous,
rational-invariant adelic functions on the `GL_n` group scheme. It requires
convergent vanishing constant terms for every actual proper rational
parabolic, using its canonical ambient radical image and intrinsic mass-one
quotient measure. The target is the original matrix
`cuspidalSubrepresentation`, whose defining condition uses every positive
standard maximal two-block split.

The universal `ParabolicDynamicStatement` premise remains explicit.
Geometric connected reductivity of this actual `GL_n` is an explicit proof
parameter, discharged in the Library by `isConnectedReductive_generalLinear`.
The comparison also retains the existing
`CompactSpace (AdeleQuotient F)` premise. It does not impose a positivity
condition on `n`; all positive block assertions are quantified only over
splits with both block sizes positive.

For each such split,
`hasVanishingNormalizedParabolicConstantTerm_generalLinearTwoBlock_iff`
compares convergence and vanishing on the corresponding actual proper
parabolic with the original matrix vanishing condition. The proof uses
the all-test two-block radical identity. It first quantifies over an
arbitrary subgroup functor and its closedness proof, then eliminates that
equality. This also transports the closedness instance used by the
normalized Haar construction. The unfolded `properParabolicQuotientMeasure`
is then exactly the intrinsic normalized measure on the existing block
subgroup, independently of the closedness proof. The intrinsic constant-term
comparison applies with its established original matrix integral,
normalization and independent absolute-convergence theorem. No measure
equality or radical identification is assumed.

`normalizedGeneralLinearParabolicCuspidal_le_standardBlock` evaluates the
all-proper condition at those actual proper parabolics.
`normalizedGeneralLinearParabolicCuspidalMap` composes this inclusion with
the existing standard-block cuspidal linear equivalence. It is a complex
linear injection. Its value theorem identifies the underlying function
with `continuousGeneralLinearEquiv`, and the evaluation theorem gives the
same complex value at corresponding actual adelic points.

The right-action theorem uses the positive convention
`R(g)f(x) = f(x * g)` on both sides, for the full adelic group.
`normalizedGeneralLinearParabolicCuspidalIntertwiner` bundles this same
injection with the original representation pulled back along the actual
adelic point homeomorphism.

This is an internal composition of the actual proper-parabolic construction,
the canonical radical identification, the intrinsic normalized block integral
comparison and the original continuous cuspidal comparison. It proves the
forward injection only. A reverse implication would additionally require
control of all nonstandard rational parabolics and their integrals; no such
classification or reverse implication is claimed. There is no new finite-volume,
reduction, growth, differentiability, tensor-realization or Hilbert comparison
assertion.
