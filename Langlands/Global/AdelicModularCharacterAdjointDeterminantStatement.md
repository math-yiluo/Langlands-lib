# The analytic modular character on actual adelic group points

Author: Worker 107.

`AdelicGroupPoints.AdelicModularCharacterAdjointDeterminantStatement`
is the analytic comparison in Getz–Hahn, *An Introduction to Automorphic
Representations* (2024), equation (3.12), printed p.89, combined with the
actual rational character in equation (3.13), p.90. It is stated for every
number field in universe `u` and every smooth connected affine group
whose structure morphism is locally of finite type. The group may be
nonreductive, nonsplit, anisotropic or zero dimensional.

The left side is Mathlib's `Measure.modularCharacter` of the existing
`AdelicGroupPoints F G`, with its existing global-function evaluation
topology. Its value at `g` is the nonnegative real scaling factor in
`Measure.map (fun x => x * g) μ = Δ(g) • μ` for an inner regular left
Haar measure `μ`. This is the Getz–Hahn convention: the pushforward
assigns a set `E` the measure of `E * g⁻¹`.

The right side uses `Lie.adjointDeterminantCharacter G`, the actual
group-scheme character of conjugation on the dual-number Lie kernel.
It evaluates that character on the actual adelic point, applies the
existing normalized idelic absolute value, and takes the underlying
nonnegative real value of the resulting unit. In particular the complex
places use their existing squared normalization. The comparison does
not introduce a substitute point carrier, a new topology, a chosen
product Haar measure or a supplied right-invariance assumption.

This proposition definition asserts no proof. Its analytic content must
still be established: the determinant must compute local Haar scaling
on actual point groups, and the local scalars must give the modular
character of the actual adelic group with the normalized idele norm.
Proposition 3.6.1, printed p.88, supplies the source's local
differential-form argument. The product of local Haar measures in
equation (3.11), p.89, gives its passage to (3.12). Haar uniqueness makes
the resulting modular character independent of the Haar normalization.
These are obligations of a proof of the statement, not premises
silently supplied by the character construction.

The two supporting lemmas implement the final ambient-group reduction
only. Given the pointwise analytic comparison and algebraic equality
`Lie.adjointDeterminantCharacter G = 0`, the published
`characterNorm_zero` lemma makes the modular character one.
Mathlib's right-translation scaling formula then proves right invariance
of the fixed `Measure.haar` on the existing adelic group. Neither lemma
proves the comparison or algebraic triviality. Passing to Haar measure
on the norm-one subgroup requires a further subgroup modular comparison
and is not asserted by these lemmas.

The source's standing hypothesis in §3.6 is a smooth affine group over
a global field. This statement retains the connected number-field
scope of the host Haar-unimodularity task. The October 2026 author
errata has no correction to §3.6.

Sources: `getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`,
§3.6, printed pp.87–90, especially Proposition 3.6.1 and equations
(3.11)–(3.13); `getz-hahn-2024-errata-2026-10`, SHA-256
`e641ec2a5485443f792935afe5ae4940323755968f784ce290a96d9cd76fc1c2`,
all five pages.
