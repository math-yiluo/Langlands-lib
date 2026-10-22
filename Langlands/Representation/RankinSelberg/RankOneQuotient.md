# The actual rank-one unipotent quotient measure

Worker 31 derives the rank-one case of the quotient-measure construction.
Independent review and publication of this pair are required.

The input is the actual group of invertible one-by-one matrices over a
nonarchimedean local field, with the actual upper-unipotent subgroup. Its
diagonal condition forces that subgroup to contain only the identity. The
matrix multiplication formula also proves that the ambient group is
commutative, so its already constructed normalized left Haar measure is
right invariant.

The integral unipotent subgroup is the whole singleton group. Its proved mass
one normalization identifies the existing `unipotentHaar F 0` with unit Dirac
mass, without changing the normalization. The actual left coset quotient is
canonically homeomorphic to `GL₁`. `rankOneQuotientHaar` transports
`generalLinearHaar F 0` along the inverse of this homeomorphism.
The image of the actual integral matrix subgroup is proved to have quotient
mass one.

The module proves every field of `QuotientIntegration.IsCompatible` for these
actual measures: nonzero mass, regularity, right invariance, integrability of
the descended orbit average of a continuous compactly supported complex
function, and the Weil integral formula. The orbital integral is simply the
original function because the unipotent measure is unit point mass. Integration
through the homeomorphism proves both the integrability assertion and the
formula. Existence is then witnessed by this constructed measure, not by an
unproved selection premise.

This is the rank-one instance of the Library's trivial-subgroup construction
`QuotientIntegration.trivialQuotientMeasure` and its compatibility theorem
`trivialQuotientMeasure_isCompatible`: both push the ambient Haar measure
forward along the homeomorphism from the ambient group to its quotient by a
trivial subgroup. The upper-unipotent subgroup equals `⊥` only by the proved
theorem `upperUnipotent_one_eq_bot`, so its left-coset quotient is not
definitionally the quotient by `⊥`. This module therefore performs the same
transport for the actual subgroup `upperUnipotent 1 F`, with the unipotent
measure `unipotentHaar F 0` (proved equal to the unit point mass used there)
and the JPSS normalization of `GL₁(O_F)`.

The original convention is JPSS, *Rankin–Selberg Convolutions* (1983), printed
page 387, §2.4, where integration is over `N_r \ GL_r`. Source
`jpss-1983-rankin-selberg`, SHA-256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
The quotient-measure formulation follows the left-coset convention explained
in `Analysis/Local/QuotientMeasure.md`, derived from Folland, *A Course in
Abstract Harmonic Analysis*, second edition (2015), §2.6, printed pages 60–63,
especially Theorem 2.51 and formula (2.52). Source
`folland-2015-abstract-harmonic-analysis-second`, SHA-256
`c82467bfa77428c32d3e1a5d1cbdc11129511e0c61da2f9d8fbc717776b9e542`.
These originals were read directly. The elementary rank-one derivation here
is internal rather than a separate assertion quoted from either source.

This construction makes no assertion of general-rank quotient-measure
existence, convergence, rational continuation, a local factor, or a functional
equation. The field lies in the explicit universe `uF` and satisfies the
project's nonarchimedean-local-field class. The ambient group, unipotent group
and quotient have explicit measurable structures and Borel-space hypotheses.
The compatibility assertion concerns continuous compactly supported
complex-valued test functions.

The companion `RankinSelberg.Measures` pair supplies the actual normalized
Haar inputs in this contribution. `Langlands.Analysis.Local.QuotientMeasure`
and all other project dependencies are published Library imports. Their
published Lean sources match those used for native compilation.

The final private native build, using pinned Lean 4.34.0 and the existing
Mathlib cache, exited successfully with no diagnostics. This is development
compilation, not independent mathematical acceptance.
