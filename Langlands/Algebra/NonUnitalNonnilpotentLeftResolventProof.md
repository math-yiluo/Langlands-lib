# Renard B.III: the original nonunital one-sided shift

`Langlands.Renard.nonUnitalNonnilpotentLeftResolvent` proves exactly
`NonUnitalNonnilpotentLeftResolventStatement A` from the unchanged published
`Langlands.Algebra.NonUnitalSeparationStatements`. It retains arbitrary
`A : Type uA` with `NonUnitalRing A`, `Module ℂ A`,
`IsScalarTower ℂ A A` and `SMulCommClass ℂ A A`.

## Source and implemented proof

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
B.III, printed p. 273 / PDF p. 279, first adjoins a scalar unit and obtains
a nonzero scalar shift without a left inverse. The original algebra and
module conventions appear on printed pp. 5–6 / PDF pp. 11–12 and I.2.1,
printed p. 14 / PDF p. 20. These passages were read directly for this proof.
The original statement documentation records the older-edition correction
removing the right-zero-divisor claim; the 2026 version governs here.

For `U = Unitization ℂ A`, the proof uses
`Langlands.Algebra.unitization_countableRank_iff` to transfer
`Module.rank ℂ A ≤ Cardinal.aleph0` to `U`, and
`Langlands.Algebra.isNilpotent_inr_iff` to transfer original positive-product
nonnilpotence to `Unitization.inr a`. It then applies the published
`Langlands.Renard.nonnilpotentLeftResolvent` at the actual algebra `U`.
Thus it obtains `z ≠ 0` such that every `b : U` satisfies
`b * (Unitization.inr a - algebraMap ℂ U z) ≠ 1`.

This is a derived adapter of Renard's first step. It reuses the published
one-sided engine rather than duplicating its algebraic or transcendental
proof. It adds no nontriviality, commutativity, finite-dimensionality,
nonzero-action or two-sided-invertibility premise. The rank comparison
also applies to a zero original algebra.

Worker 1210 implemented the adapter. Worker 709 supplied the original
statement and proposed unitization route, with Worker 6's source and
original-action clarification. The imported one-sided engine is Worker
972's proof; its authorship is unchanged. The actual quotient and original
additive simplicity are established in the subsequent quotient proof.

## Verification

In environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, the development check
compiled this module with zero errors and warnings. Declaration inspection
retains the sole universe parameter `uA` and uses only `propext`,
`Classical.choice` and `Quot.sound`. Independent semantic review and the
submission's exact-target and Lake checks are separate publication gates.
