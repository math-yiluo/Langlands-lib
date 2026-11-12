# Irreducibility detected by compact-open fixed corner modules

Author: Worker 136. The theorem `Langlands.Hecke.irreducibleIffFixedSimple`
proves exactly `Langlands.Hecke.IrreducibleIffFixedSimpleStatement.{u,v}`,
including both zero cases and retaining independent universes.

The source assertion is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, III.1.5, Theorem (i), printed p.61 / PDF p.67.
The source is registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 136 read PDF pp.66–67.

For the forward implication, a zero carrier has zero fixed subspaces. For an
irreducible representation, each nonzero fixed space is simple by the published
theorem `CompactCoefficientClass.isSimpleModule_fixedVectors`. Despite its containing
module's name, that theorem has no compact-coefficient hypothesis. Zero fixed spaces
are handled separately.

For the converse, the zero carrier is immediate. Otherwise the invariant-submodule
lattice is nontrivial. Let `S` be a nonzero subrepresentation and choose a nonzero
vector `x` in it. For any ambient vector `y`, smoothness gives open fixing subgroups
for `x` and `y`. The published Van Dantzig theorem
`Topology.LocallyProfiniteProof.vanDantzig` supplies a compact open subgroup `K`
contained in their intersection. Both vectors are therefore `K`-fixed, and the
fixed space is nonzero.

Inside that fixed space form the corner submodule whose underlying vectors belong
to `S`. Closure under the corner action follows from the published preservation
lemma `CompactCoefficientSemisimplicity.integratedAction_mem`, which preserves
every subrepresentation and has no compact-coefficient hypothesis. This corner
submodule contains `x` and hence is nonzero. Simplicity makes it the whole fixed
space, so it contains `y`. Since `y` was arbitrary, `S` is the whole representation.
Mathlib's `IsSimpleOrder.of_forall_eq_top` packages the resulting irreducibility.

The proof imports the unchanged target module, the two published
compact-coefficient modules containing the general lemmas just described, and the
locally profinite topology proof. No imported files are edited and no assumptions
are added.
