# Split-component lifts modulo the compact norm kernel

Author: Worker 1682.

This internal supporting module works with a supplied compatible
`ParabolicRootPresentation`. It does not assert that presentations exist
or prove Casselman's criterion.

An integral cocharacter of the ambient maximal split torus that annihilates
the selected roots is central in the represented standard Levi. The
published centrality theorem uses finiteness of the simple roots and
existence of a simultaneous standard cocharacter, both supplied by the
presentation. The universal factorization property of its split component
then lifts this cocharacter integrally. This includes directions on the
boundary of a chamber.

The published intrinsic uniformizer section represents every point of the
ambient split torus modulo the common norm kernel. Its character orders
are the integer pairings with the corresponding cocharacter. If the
selected-root orders of the original point vanish, that cocharacter
annihilates the selected roots and hence lifts to the split component.
Naturality of uniformizer evaluation gives a representative coming from
the component itself. The defined point
`splitComponentPointRepresentative` chooses such a uniformizer
representative in the actual split component. Its accompanying theorem
proves the compact norm-kernel relation.

The remaining two lemmas concern a smooth complex character of any closed
subgroup of a split torus. The intersection of that subgroup with the
common norm kernel is compact. Such a character has norm one on this
intersection, by the published compact-subgroup character lemma.
Consequently its modulus is equal at two subgroup points whose ratio
belongs to the common norm kernel.

These are internal deductions from existing Library constructions, with
no assertion of equivalence to a new original-source statement. The
selected-root order condition, the supplied presentation and closedness
hypotheses remain explicit. Identifying actual central test points with
these hypotheses and connecting the comparison to the full analytic
criterion remain separate steps.
