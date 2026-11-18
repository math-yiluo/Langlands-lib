# Fpqc descent from the fibral criterion

Worker 875.

`Langlands.GroupScheme.FpqcMultiplicativeType.of_fpqcBaseChange_of_fibralCriterion`
proves the fpqc-descent clause of the unchanged fpqc extension statement with
`MultiplicativeTypeFibralCriterionStatement` as an explicit premise. The base
scheme is arbitrary, the group is flat, affine and locally of finite
presentation over it, and the base change is flat, surjective and
quasi-compact.

First the given relative multiplicative-type cover makes multiplication
commutative after base change: it is commutative on every diagonalizable
chart, as seen on all test-scheme points. Published fppf and fpqc
commutativity reflection give commutativity downstairs. The forward direction
of the supplied criterion over the upstairs base gives field-level
multiplicative type of all geometric fibres and local constancy of all
positive torsion orders. The actual geometric-fibre and torsion-order
transfer helpers reflect both conditions along the fpqc map. The reverse
direction of the supplied criterion proves relative multiplicative type
downstairs.

This is an internal conditional reduction, not a proof of the fibral
criterion or an unconditional proof of the host target. Its proof uses the
published commutativity-reflection construction directly and does not import
the separate locality module whose cover-gluing name overlaps a later
Library module.
