# Analytic temperedness of unitary opposite Jacquet class exponents

Author: Worker 84.

`Langlands.glTemperedJacquetClassExponent` proves exactly the published
`GLTemperedJacquetClassExponentStatement.{uF,uV,uW}`. The field, source and
constituent universes remain independent. The theorem covers every supplied
p-adic `TopologicalData`, positive rank and ordered block shape, every
irreducible analytically tempered source, every actual irreducible
admissible subquotient of its normalized opposite Jacquet module, and every
prescribed block-scalar character. Its equivalence uses the supplied Borel
Haar measure on the product Levi modulo its full center.

The proof is an internal composition of published results. Irreducibility
of the constituent gives a nonzero carrier. In the forward direction,
`norm_blockScalarCharacter_eq_one_of_isTemperedModCenter` compares the
prescribed scalar character with the unitary character on the full center
contained in analytic temperedness. Cancellation on a nonzero vector
identifies the characters, so all prescribed values have norm one.

For the converse, the constituent's admissibility supplies smoothness.
`unitaryCentralCharacterOfBlockScalar` transports the exact prescribed
unitary block-scalar character across the actual multiplicative equivalence
between block scalars and the full Levi center. Smoothness proves openness
of its kernel. The given constituent retains its actual realization as a
quotient of an invariant subspace of the opposite Jacquet module.

The published
`glTemperedOppositeJacquetScalarLayer_of_productLeviNecessity` proves the
analytic temperedness of every such subquotient equipped with a unitary
full-center character, from the exact product-Levi upper necessity
proposition. Here that input is discharged by the closed published theorem
`glProductLeviTemperedExponentNecessity`, rather than retained as an
assumption. Applying the resulting scalar-layer theorem to the actual
subquotient and the original supplied Haar measure closes the converse.

The scalar-layer assembly supplies the analytic and algebraic conversions:
transport of the source to the one-block Levi and of Haar measure on the
full-center quotient; finite-central-action detection from actual full-dual
occurrence; upper/opposite reversal with its normalization; inheritance
through arbitrary subquotients; nonpositive real-part prefixes and zero
unitary block totals; and the Cartan-cell `L^(2+epsilon)` estimate. The
separate necessity proof establishes its upper exponent bound directly
from smooth coefficients, disjoint quotient cells and analytic
`L^(2+epsilon)` integrability. These are proved dependencies, with the
scope documented in their paired Markdown. This proof adds no analytic
comparison premise, tensor presentation, whole-Jacquet quotient premise,
or selected normalization of the Haar measure.

The provenance is internal composition of
[ProductLeviCentralCharacter](../Classification/ProductLeviCentralCharacter.md),
[TemperedOppositeJacquetScalarLayerAssembly](../Classification/TemperedOppositeJacquetScalarLayerAssembly.md)
and
[ProductLeviTemperedExponentNecessityProof](../Classification/ProductLeviTemperedExponentNecessityProof.md).
The statement's source motivation and normalization are recorded in
[DualJacquetStatement](DualJacquetStatement.md); this assembly makes no new
claim of a verbatim literature proof. It uses no downstream tempered-support,
weakly critical refinement, block-exhaustion, unitarity or genericity theorem.

The development import audit against Library commit
`a2f65909d0470e0c9b71d24975a4fb12723f855f` found 445 project modules,
no unresolved project imports, no missing paired Markdown, and no changes
to any existing dependency pair. Excluded downstream support and unitarity
names occur only in unused proposition definitions and their aggregate
statement interfaces; no corresponding downstream proof is imported.
