# Inversion densities of actual Haar measures

This internal target uses Mathlib's actual `modularCharacter` on a locally
compact Hausdorff second countable topological group with its Borel measurable
structure. For every actual left Haar measure `μ` it asserts the two equalities
of measures

\[
\mu^{\mathrm{inv}}=\Delta\,\mu,\qquad
\mu=(g\mapsto\Delta(g^{-1}))\,\mu^{\mathrm{inv}}.
\]

Here inverse measure means pushforward by group inversion and multiplication
of a measure by a function means `Measure.withDensity`. There is no unknown
scalar, supplied density identity, or unimodularity hypothesis. The second
equality is the inversion-density formula for the actual right Haar measure
`μ.inv`; inversion of `μ.inv` is identified by the existing
involution theorem with `μ`. The group universe is arbitrary.

Mathlib defines `Δ(g)` by right pushforward of a left Haar measure:
`map (· * g) μ = Δ(g) • μ`. In the right Haar convention of Getz--Hahn,
section 3.2, printed pp.81--82 / PDF pp.97--98, this is the character
`δ_G`; their equation (3.8) reads `dr = δ_G dl`. Consequently the second
formula uses `Δ(g⁻¹) = Δ(g)⁻¹`, as required by the Hermitian equation in
section 9.3, printed pp.246--247 / PDF pp.258--259. This is an internal
general Haar-measure target, not a claim that the book's smooth adelic
action has been constructed.

The intended proof uses the published general continuity theorem
`Langlands.Haar.continuous_modularCharacter_of_locallyCompact`. Weighting
`μ` by `Δ` gives a locally finite right invariant measure. The inverse
is left invariant and, by Haar uniqueness, is a scalar multiple of `μ`.
Transport of densities under inversion and the identity
`Δ(g)Δ(g⁻¹)=1` show that this scalar has square one. Positivity and finite
positive mass of a compact identity neighborhood force the scalar to
be one. A final density cancellation gives the right Haar formula.
Second countability ensures the regularity needed for Haar uniqueness.

The provenance is internal, derived from pinned Mathlib's Haar uniqueness,
modular-character definition, and change-of-variables and density laws.
The source convention and intended application are from registered
`getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`,
at the locators above. The complete registered October 2026 errata,
`getz-hahn-2024-errata-2026-10`, SHA-256
`e641ec2a5485443f792935afe5ae4940323755968f784ce290a96d9cd76fc1c2`,
does not change these assertions. An exact-target proof, actual automorphic
realizations, smooth weights and compactness remain separate obligations.
