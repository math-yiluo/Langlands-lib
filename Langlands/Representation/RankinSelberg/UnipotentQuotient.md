# The unipotent quotient measure in every rank

This module constructs the measure on the actual left quotient
`N_(n+1) \ GL_(n+1)(F)` using the published normalized ambient and subgroup
Haar measures, for every natural `n` and nonarchimedean local field `F`.
The measurable structures on the two groups and quotient are arbitrary Borel
structures for their existing topologies.

The source is Folland, *A Course in Abstract Harmonic Analysis*, second edition
(2015), Section 2.6, Proposition 2.50 and Theorem 2.51, printed pp. 62–63,
including formula (2.52). The registered source is
`folland-2015-abstract-harmonic-analysis-second`, SHA256
`c82467bfa77428c32d3e1a5d1cbdc11129511e0c61da2f9d8fbc717776b9e542`.
Folland uses `G/H` and left translation; the Library uses cosets `H*g`,
averages `f(h*g)`, and right translation. Inversion exchanges the conventions;
the supplied Haar measures are both two-sided invariant by the imported
general-linear and unipotent unimodularity proofs.

The implemented construction specializes the already proved real positive
lifting and averaging-kernel theorems. The integral therefore descends along
the real averaging map to a positive functional. `unipotentQuotientHaar` is
`measureOfPositiveAveraging`, hence the Riesz–Markov–Kakutani measure of that
functional. This is an internal specialization of the Library construction,
with all lifting and kernel hypotheses discharged.

The real integration formula is the Riesz representation identity. Nonzeroness
follows from an ambient compact test with nonzero integral, since the integral
matrix subgroup has ambient mass one. Right translation commutes with
averaging and preserves ambient integration, so uniqueness in Riesz
representation gives right invariance. Compactness and continuity of real
averaging and its complexification give integrability and the complex Weil
formula. `unipotentQuotientHaar_isCompatible` assembles these five fields;
`unipotent_compatibleMeasureExists` supplies the constructed measure as witness.

For uniqueness, the complex compatibility identity applied to a real test
function, viewed in `ℂ`, gives the real identity. Surjectivity of averaging and
uniqueness of regular measures from compact continuous test integrals then
identify any compatible measure with `unipotentQuotientHaar`.
`unipotentQuotientHaar_zero` applies this uniqueness to the published
`rankOneQuotientHaar_isCompatible` proof. Thus agreement in rank one is equality
of the actual measures with their fixed normalizations.
