# Renard III.3.1–III.3.2: proof of the equivariant sheaf and test-module equivalences

Worker 134 implemented this proof. The entry theorem is
`Langlands.Sheaf.Renard.EquivariantModuleStatements.statements :
Statements.{uG}`. It proves the published proposition
`EquivariantModuleStatements.Statements` from
`EquivariantModuleStatements.lean` exactly as stated, for every group
universe `uG`. The proposition is the conjunction of `AlgebraicStatement` and
`SmoothStatement`.

## Source

The governing original is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026. III.3.1 is on
printed p.83 / PDF p.89 and III.3.2 on printed p.84 / PDF p.90. The
registered source is `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Renard deduces the equivariant correspondence from the II.2.5 equivalence
in one sentence. The proof follows that route.

## The implemented proof

The theorem is
`EquivariantModuleEquivalence.statements_of_comparisons` from the helper
module `EquivariantModuleEquivalence`, applied to two published proofs:

- `CompactSectionEquivalence.sheafComparisonIsIso`, the II.2.5 proposition
  that every ordinary comparison `F ⟶ P(Γc F)` is an isomorphism;
- `ModuleProjectorComparison.moduleComparisonIsIso`, the II.2.5 proposition
  that every ordinary comparison `M ⟶ Γc(P M)` is an isomorphism.

The helper module shows that both comparisons commute with the original
group operators. They become the unit and inverse counit of
`CategoryTheory.Equivalence.mk` applied to the published functors
`CompactSectionActions.functor hX` and `ProjectorActionSheaf.functor hX`.
The same unit and counit, restricted to the published whole-module smooth
full subcategories, give the equivalence between
`CompactSectionActions.smoothFunctor hX` and
`SmoothProjectorActionSheaf.smoothFunctor hX hG`. In both cases the functor
and the inverse are the published functors by `rfl`, as the statements
require. Its paired Markdown `EquivariantModuleEquivalence.md` describes the
construction in detail.

No premise is added to the published statements. No inverse functor law,
comparison certificate or equivalence is assumed. The group premise `hG` of
`AlgebraicStatement` is not used by the algebraic equivalence; it is used,
through `SmoothProjectorActionSheaf.smoothFunctor`, only in the smooth
statement.
