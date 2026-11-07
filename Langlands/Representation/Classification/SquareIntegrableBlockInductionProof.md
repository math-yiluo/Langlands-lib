# Normalized induction of square-integrable GL blocks

Author: Worker 162.

`Langlands.Classification.squareIntegrableBlockInduction` proves the published
proposition `Langlands.Classification.SquareIntegrableBlockInduction.{uF,uV} F T`
from [TemperedBlockStatement](TemperedBlockStatement.md). Its outer parameters
are exactly `{p} [Fact p.Prime] (F : PadicField.{uF} p)
(T : F.TopologicalData)`. For every positive total rank, ordered block shape
and family of irreducible analytically square-integrable unitarizable blocks,
it proves all three conclusions: irreducibility, existence of an invariant
positive Hermitian form, and analytic temperedness of the actual normalized
product induction.

The first conjunct applies
`Langlands.Classification.squareIntegrableBlockInductionIrreducibility` from
[SquareIntegrableInductionIrreducibilityProof](SquareIntegrableInductionIrreducibilityProof.md)
directly to the original blocks. That published proof uses analytic segment
classification, nonlinkage and the segment-head product criterion, retaining
the original ordered family by equality transport of its ranks.

The second conjunct applies the product clause of
`Langlands.glNormalizedInductionUnitarity` from
[UnitaryProof](../Induction/UnitaryProof.md) to the block form hypotheses.
This theorem supplies an actual invariant positive form on the induced
representation. Its construction uses the positive form on the full finite
algebraic tensor product and scalar compact integration.

The private helper `blockInduction_tempered` proves the third conjunct.
Analytic square-integrability supplies admissibility of each block.
`Langlands.admissibleSchur_scalarEndomorphism` gives scalar self-intertwiners,
and `Langlands.FiniteTensor.isIrreducible_external` proves irreducibility of
the actual block tensor.

The helper equips the full central quotient of the actual Levi with its
Borel measurable structure and chooses an existing Haar measure using
`T.exists_isHaarMeasure_leviCentralQuotient`. At this same measure:

1. The forward implication of `Langlands.glBlockTensorSquareIntegrable`
   proves analytic square-integrability of the block tensor.
2. `Langlands.glLeviDiscreteSeriesTempered` proves its analytic temperedness.
3. `Langlands.glTemperedInductionPreservation` proves `T.IsTempered` of its
   actual normalized induction.

These inputs are proved in
[BlockTensorSquareIntegrableProof](BlockTensorSquareIntegrableProof.md),
[LeviDiscreteSeriesTemperedProof](LeviDiscreteSeriesTemperedProof.md), and
[TemperedInductionPreservationProof](TemperedInductionPreservationProof.md).
The last proof composes the analytic product-Levi criterion, preservation of
upper Jacquet bounds through the normalized geometric lemma, and the ambient
analytic exponent criterion. The normalized product induction in the target
is definitionally the normalized induction of this block tensor.

The field and representation universes remain independent, with block
carriers in `Type (max uF uV)`. The analytic input theorems are instantiated
at `uF, max uF uV`; the form theorem uses `uF, uV`. The helper's conclusion
is the original `T.IsTempered`, including all ambient Borel Haar measures,
all actual smooth-dual coefficients, and every positive epsilon. Choosing a
Levi quotient measure introduces no additional premise. The supplied topology,
full centers, standard upper parabolic, positive half-modulus covariance and
right-translation action are retained throughout.

This is a derived composition of published Library proofs; their paired
Markdown files document the original sources and implemented arguments.
The local helper only assembles these analytic APIs. No parent induction,
tempered exhaustion, genericity or uniqueness theorem is used to discharge
the target, and no theorem-valued hypothesis is added. Only this new
Lean/Markdown pair is contributed; the target statement and its imports are
unchanged.
