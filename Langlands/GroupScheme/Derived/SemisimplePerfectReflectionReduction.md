# Semisimple perfectness from actual reflections and torus generation

Authors: Worker 1484 (assembly); Worker 1449 (reused semisimple
reflection-to-root-datum reduction).

This module proves a conditional reduction, not the unconditional
semisimple-perfectness theorem. Its two explicit premises are the published
`RelativeRootReflectionExistenceStatement.{u}` and
`ReductiveFiniteTorusGenerationStatement.{u}`. They remain proof obligations.

`SemisimplePerfectReflectionReductionStatement.{u}` names their implication
to the unchanged published `SemisimplePerfectStatement.{u}`.
`semisimplePerfect_of_reflectionExistence_of_torusGeneration` proves this
implication in arbitrary universe `u`.

Over an algebraically closed field, every maximal torus splits by the
published finite Galois splitting and split-reflection proofs. It is
therefore a maximal split torus, so the reflection-existence premise gives
actual integral reflection data for its inclusion. The additional
full-root-kernel centralizer property supplied by that premise is not used
in this assembly.

Worker 1449's `RelativeRootReflectionData.exists_semisimple_rootDatum`
then constructs an actual root datum with finite integral coroot quotient,
using semisimplicity, splitness and closedness. No reducedness theorem or
general character-complement theorem is needed. The finite-coroot-index
containment theorem in `SemisimpleTorusContainment` places this maximal
torus in the full derived subgroup on every test scheme.

`algebraicallyClosedSemisimpleMaximalTorusDerived_of_reflectionExistence`
formalizes this step. The closing conditional theorem passes that
containment result and the torus-generation premise to
`semisimplePerfect_of_maximalTorusDerived_of_torusGeneration`.
The latter extends each generating torus to a maximal torus, tests every
closed commutator-containing subgroup, and descends from the algebraic
closure by fpqc descent.

All actual scheme-theoretic centres, torus inclusions, normalizer points,
commutators and subgroup functors are the existing Library constructions.
The final conditional conclusion retains every field, every characteristic,
imperfect fields and the full test-scheme equality. The provenance is an
internal composition of the named reductions. It makes no claim that the
two explicit structural inputs have been proved.
