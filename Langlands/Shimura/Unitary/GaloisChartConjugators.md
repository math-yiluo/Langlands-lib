# Conjugating matrices for Galois-shifted Harris charts

This internal construction uses the actual Harris signature charts `C`, a compatible
CM section `hΦ`, and a finite basis `b` of the original algebra over the totally real
field. For every rational algebra automorphism `s` of the complex numbers and every
CM embedding `i`, the existing `embeddingChartComparison` is a complex-linear
algebra automorphism of the full matrix algebra.

`embeddingChartConjugator` chooses a matrix unit supplied by
`Langlands.MatrixAlgebra.exists_unit_conj_of_algEquiv` for that automorphism.
Its specification `embeddingChartComparison_conj` holds for every matrix:
the chart comparison is multiplication by the chosen unit on the left and
its inverse on the right. The unit is independent of the matrix.

`embeddingFactorGaloisEquiv_conj` combines this specification with
`embeddingChartComparison_map`: factor transport first applies `s` entrywise
and then conjugates by the chosen unit. `embeddingMatrixGaloisEquiv_conj`
gives the corresponding formula for a full matrix array, evaluated at
the shifted embedding `s ∘ i`.

The construction uses classical choice from the proved innerness theorem;
it assumes neither a conjugating matrix nor compatibility of chart choices.
No uniqueness, cocycle identity, or simultaneous realization by an actual
similitude group point is asserted.

The provenance is internal: this specializes the matrix-algebra innerness
result to the already constructed chart comparison and composes its
established factor-transport identities. The imported matrix-innerness proof
is the published module `Langlands.Algebra.MatrixAlgEquivInnerProof`.
