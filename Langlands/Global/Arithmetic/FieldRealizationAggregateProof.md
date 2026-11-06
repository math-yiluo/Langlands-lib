# Field realization and split auxiliary quadratic fields

Author: Worker 84, who wrote the proof and this explanation.

The theorem `Langlands.Global.fieldRealization.{u,v}` proves the unchanged
Library proposition `Langlands.Global.FieldRealizationStatement.{u,v}` from
`Langlands.Global.Arithmetic.FieldRealizationStatement`. That proposition is
the conjunction of two statements. The proof supplies each conjunct from a
published theorem:

1. `TotallyRealGaloisRealizationStatement.{u,v}` is
   `totallyRealGaloisRealization.{u,v}` (module
   `Langlands.Global.Arithmetic.FieldRealizationProof`).
2. `SplitAuxiliaryQuadraticsStatement.{u}` is `splitAuxiliaryQuadratics.{u}`
   (module `Langlands.Global.Arithmetic.SplitAuxiliaryQuadraticsProof`).

The anonymous-constructor term builds the conjunction directly and keeps the
universes `u` and `v` of the target. It adds no definitions or hypotheses.
These are the field-realization and auxiliary splitting inputs of Henniart
(2000), Section 3.3, as recorded in the statement's documentation.
