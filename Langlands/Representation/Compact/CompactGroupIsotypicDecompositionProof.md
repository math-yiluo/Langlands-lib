# The compact-group isotypic decomposition

Author: Worker 88. This proves the exact published proposition
`Langlands.Renard.CompactRepresentation.CompactGroupIsotypicDecompositionStatement`
without changing its hypotheses or its independent group and carrier universes.
The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, IV.1.1 Corollary, printed pp.88–89 / PDF pp.94–95,
registered as `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

The implemented proof uses the published compact-coefficient decomposition
infrastructure. Equip the compact group with its Borel measurable structure
and a Haar measure normalized on the whole group. These are constructed inside
the proof, not additional premises. Each open subgroup is closed and hence
compact, so compact open subgroups are cofinal among open subgroups.
Every smooth coefficient has compact topological support because its domain
is compact. The published
`totalIsotypicSubrepresentation_eq_top_of_compactCoefficients` therefore shows
that the intrinsic isotypic subrepresentations span the whole representation.
Its representatives have the same carrier universe as the ambient object,
exactly as required by the target.

For independence, fix a class `c`. The published
`isCompl_isotypicSubrepresentation_annihilatorSubrepresentation` gives
complementarity of its isotypic part with its annihilator.
Schur's lemma, in the published
`isotypicSubrepresentation_le_annihilator_of_ne`, places every other isotypic
part in that annihilator. Their supremum also lies there and is therefore
disjoint from the `c`-isotypic part. The defining criterion `iSupIndep_def`
concludes independence. Passing to underlying submodules reflects equality,
so this is independence in the target's subrepresentation lattice.

This is an internal derivation using existing Library proofs; it takes a
different route from Renard's proof by grouping a chosen irreducible direct
sum by isomorphism class. It adds no countability, admissibility, measure,
or unimodularity assumption to the compact-group statement.
