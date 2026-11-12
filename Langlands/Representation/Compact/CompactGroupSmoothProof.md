# Smooth compact-group representations and finite multiplicities

Author: Worker 88. `compactGroupSmoothStatements` proves the exact Library
proposition `Langlands.Renard.CompactRepresentation.CompactGroupSmoothStatements`.
It is the conjunction of the exact IV.1.1 and IV.1.2 proof terms from the
companion modules, in the order of the published statement, with the same
independent group and carrier universes and no additional premises.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, IV.1.1 Theorem and IV.1.2 Proposition,
printed pp.88–89 / PDF pp.94–95, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

`compactGroupSmoothRepresentation`, from
`CompactGroupSmoothRepresentationProof`, proves the four IV.1.1 assertions:
finite dimension of irreducibles by finite compact orbits; an open normal
trivial-action subgroup by a finite basis and the action kernel;
semisimplicity by the published compact-coefficient semisimplicity theorem;
and unitarizability by constructing an algebraic positive form and averaging
it over inverse orbits with Haar measure constructed internally. Its paired
Markdown gives the implemented arguments and the exact meaning of the
invariant Hermitian core.

`admissibleFiniteMultiplicity`, from `AdmissibleFiniteMultiplicityProof`,
proves the IV.1.2 equivalence. Necessity uses admissibility of restriction to
an open subgroup and the published finite-type-source intertwiner-finiteness
theorem. Sufficiency tests with the irreducible trivial representation on
`ULift.{v} ℂ`, thereby respecting the independently quantified carrier
universe, to bound each compact-open fixed space. Compact-open cofinality
then proves the Library's all-open-subgroups admissibility convention.
Its paired Markdown explains the actual fixed-vector-to-intertwiner map.

The imported proof files are unchanged. The entry theorem only forms their
conjunction; it asserts all four IV.1.1 conclusions and the full IV.1.2
biconditional exactly as required by the published target.
