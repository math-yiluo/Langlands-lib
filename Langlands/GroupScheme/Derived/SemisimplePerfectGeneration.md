# Semisimple perfectness from torus containment and generation

Author: Worker 1484.

This module is a conditional reduction of semisimple perfectness. It does
not prove either structural input or the original perfectness theorem
unconditionally.

`AlgebraicallyClosedSemisimpleMaximalTorusDerivedStatement.{u}` names the
all-test assertion that every maximal torus in a semisimple group over
an algebraically closed field has range contained in the full derived
subgroup functor.

`algebraicallyClosedSemisimpleMaximalTorusDerived_of_rootDatumExistence`
derives that assertion from the explicit `RootDatumExistenceStatement`
premise. The published finite Galois splitting proof and split reflection
make every torus over an algebraically closed field split. An actual root
datum supplied by the premise then gives the containment by the
`SemisimpleTorusContainment` module. The argument does not use the supplied
root datum's reducedness.

`algebraicallyClosedSemisimplePerfect_of_maximalTorusDerived_of_torusGeneration`
takes the displayed maximal-torus containment assertion and
`ReductiveFiniteTorusGenerationStatement` as explicit premises. The latter
supplies finitely many closed tori generating `G`. Each is made a
commutative group scheme using its torus property, and the published
finite-type maximal-extension theorem embeds it into a maximal torus of
`G`. By the first premise its image lies in the derived subgroup, hence in
every closed subgroup containing the commutators. This supplies the
factorization witnesses required by the generation premise, so each such
closed subgroup has total range. The defining intersection for the
derived subgroup is therefore total.

`semisimplePerfect_of_maximalTorusDerived_of_torusGeneration` composes this
algebraically closed result with fpqc descent from
`SemisimplePerfectReduction`. Finally,
`semisimplePerfect_of_rootDatumExistence_of_torusGeneration` substitutes the
conditional root-datum argument into that reduction.

All statements retain arbitrary universe `u`. The final conditional
conclusion concerns every field, including imperfect fields and positive
characteristic, and equality of the subgroup functors on every test scheme.
The infinite-field hypothesis of finite torus generation is discharged by
algebraic closedness. No rational-point generation statement replaces its
all-test conclusion.

These are internal compositions of the named Library interfaces and the
preceding cocharacter-containment lemmas. Root-datum existence and finite
torus generation still need independent proofs before this route supplies
the unconditional semisimple-perfectness theorem.
