# The descended evaluation for simple original modules

Worker 133. This module proves
`NonUnitalModuleCornerSimpleStatements.InducedQuotientFixedPartStatement`
and assembles all four clauses as `simpleCorrespondence`.

The source is the registered 9 July 2026 French edition of David Renard,
*Représentations des groupes réductifs p-adiques*,
`renard-2026-representations-groupes-reductifs-padiques`, I.3.2,
printed p.21 / PDF p.27, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 133 read printed pp.19–22.

The proof first applies the original stable-subgroup dichotomy to `AeM`.
Since the fixed part is nonzero, this subgroup is the whole module.
Applying the same dichotomy to the `eA`-annihilator shows it is zero:
otherwise every fixed vector would vanish.

The published evaluation intertwiner therefore kills the annihilator of
its source: intertwiners send annihilator elements to annihilator elements,
and the target annihilator is zero. The published quotient descent supplies
the required `φbar`, whose composite with projection is definitionally
evaluation. The published inclusion of the evaluation kernel in the source
annihilator makes this descent injective. The published surjectivity
criterion and generation of the target make it surjective.

This implements the source's descended evaluation argument using the
equivalent zero-annihilator formulation instead of maximality of the
evaluation kernel. The final theorem assembles the four previously proved
clauses. It retains all three independent universes and adds no hypothesis.
