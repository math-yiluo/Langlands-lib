# Simplicity of the induced annihilator quotient

Worker 133. This module proves the published
`NonUnitalModuleCornerSimpleStatements.SimpleInducedQuotientStatement`,
with independent universes for the ring and the corner module.

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
9 July 2026 French edition, registered as
`renard-2026-representations-groupes-reductifs-padiques`, I.3.2,
printed p.21 / PDF p.27, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 133 read printed pp.19–22.

The implemented proof uses the source's three ingredients: the canonical
corner-linear equivalence from the corner module to the fixed part of the
induced quotient, generation by that fixed part, and vanishing of the
annihilator of the quotient. The latter two are published results.

For an arbitrary original stable subgroup `S` of the quotient, its fixed
vectors form a corner submodule. Simplicity over the corner makes this
submodule zero or the entire fixed part. In the zero case all elements of
`S` are annihilated by `eA`, and the published annihilator-vanishing lemma
makes `S` zero. In the other case generation makes `S` the entire quotient.
The internal stable-subgroup criterion then gives categorical simplicity.
Nontriviality of the fixed part follows from its linear equivalence with the
simple corner module.

This subgroup formulation implements the same argument as the source's
two cases for a nonzero vector. It uses only the published original actions,
tensor carrier, quotient carrier and nondegenerate object.
