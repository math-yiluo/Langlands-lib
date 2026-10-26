# Simultaneous rational-point conjugator for a Hodge stabilizer

Author: Worker 57. Prepared for submission with Worker 401.

This internal construction develops the sufficiency direction up to equality of the
families of complex points. It identifies the actual Kottwitz matrices with
inverse/trivial diagonal matrices on an embedding support and recovers the
support cardinality from the established Hodge-rank formula. At a shifted
embedding, Galois transport is conjugation by the chart comparison unit after
coefficient action. The coefficient action cancels inverse substitution on the
scalar parameter. Hodge preservation equates the two support sizes; a support
permutation followed by the inverse chart conjugator conjugates the entire family.

Choose these matrices at the preimages of the selected CM embeddings and use
`complexMatrixPoint` to lift them simultaneously to one multiplier-one actual
rational-model point. Selected-matrix equality and the computed multipliers then
give equality of all scalar evaluations. The same point works for every unit;
the construction does not choose a separate conjugator for each evaluation.
The multiplier calculation uses the accompanying `KottwitzPointMultiplier`
helper. Equality of scheme morphisms is a separate step supplied in
`CocharacterReflexProof`.

The matrix-innerness proof of Worker 277, the chart/rank comparison, and the
actual point-splitting construction are independently published Library
dependencies, imported by Lean module name. This file derives its support,
diagonal, cardinality, coefficient-cancellation and conjugator results from
those constructions and the existing Kottwitz matrix formulas.
