# Semisimple centralizer tangent factors and maximal tori

This internal module combines the actual affine representation theory with the
conditional Cartan tangent construction. It introduces no new external
structural assertion. The field has arbitrary universe and characteristic.

Let `G` be an affine group scheme locally of finite type over a field `k`, and
let `j : C → G` be a smooth affine closed representative of the all-test
centralizer of a representation-semisimple tangent vector `X`. Three global
statements remain explicit premises: `NilpotentCentralTorusStatement`,
`UnipotentSemisimpleStatement`, and `CartanStructureStatement`.

`Lie.semisimpleCentralizerTorusFactor` constructs a tangent preimage of `X`
in any prescribed maximal torus of the identity component of `C`. It uses
`Lie.elementCentralizerIdentityTorusFactor`, supplying its formerly explicit
self-membership premise with `Lie.mem_elementCentralizerLie_self`. For each
closed subgroup tangent lift of `X`, the ambient geometric semisimplicity test
reflects to the subgroup by
`Lie.isSemisimpleElement_of_closed_subgroup`, after rewriting the given tangent
image equality. The connectedness and geometric nilpotence of each Cartan
representative in the centralizer's identity component come from the explicit
`CartanStructureStatement` premise. The companion `targetMap` theorem gives
the exact reconstruction identity in `G`.

`preservesMaximalTori_identityComponent_elementCentralizer_of_semisimple`
applies the actual maximality adapter to those tangent preimages. Its conclusion
is `PreservesMaximalTori` for the inclusion of the centralizer's identity
component into `G`.

Finally, `isGeneratedByCartanSubgroups_of_semisimpleCentralizerSpanning`
specializes the existing semisimple-centralizer induction step. For smooth
connected affine `G`, it discharges centralizer smoothness using the proved
`Lie.semisimpleCentralizerSmooth` and maximal-torus preservation using the
preceding construction. The tangent-spanning equality and dimension-induction
hypothesis remain explicit, together with the three structural statements.
The resulting generation property still quantifies over every actual closed
competitor, including nonsmooth and nonreduced competitors.

This module proves conditional supporting results. It does not prove any of the
three retained structural statements, the tangent-spanning statement, or the
full `CartanGenerationStatement`.
