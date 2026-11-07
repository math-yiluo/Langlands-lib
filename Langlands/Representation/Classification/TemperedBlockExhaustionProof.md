# Analytic tempered exhaustion by square-integrable GL blocks

Author: Worker 69.

`Langlands.Classification.temperedBlockExhaustion` proves exactly
`Langlands.Classification.TemperedBlockExhaustion.{uF,uV} F T`.
Its outer parameters are `{p} [Fact p.Prime] (F : PadicField.{uF} p)`
and `(T : F.TopologicalData)`, with independent `uF,uV`. For every positive
rank and every irreducible analytically tempered smooth representation, it
constructs an ordered block shape, actual smooth block representations,
irreducibility, analytic square-integrability and invariant positive forms
for every block, and an actual category isomorphism to their normalized product.
All carriers remain in `Type (max uF uV)`. There is no additional premise.

The proof starts with the published
`Langlands.glTemperedDiscreteSeriesSupport`, instantiated at
`{uF,max uF uV}`. This gives an ordered shape `B`, an actual irreducible Levi
representation `σ` in the original carrier universe, square-integrability
modulo the full Levi center for every Borel Haar measure, and an injective
intertwiner from the input into normalized opposite induction of `σ`.
An existing Haar measure on the Levi central quotient supplies admissibility;
its smoothness field makes `σ` an actual `SmoothRep` object.

`CuspidalSupport.padicLeviAdmissibleFactorization` then presents `σ` by an
actual equivariant linear equivalence with `B.blockTensor` of irreducible
admissible smooth representations `A i`. For every Haar measure,
`isSquareIntegrableModCenter_of_equiv` transports square-integrability through
this equivalence. The reflection direction of
`Langlands.glBlockTensorSquareIntegrable` gives analytic square-integrability
of each original factor. Its full Borel and Haar quantifiers are retained.
`Langlands.glSquareIntegrableUnitarity` supplies an actual invariant positive
Hermitian form on each factor. The proof uses this theorem on each block,
without assuming unitarizability of the input tempered representation.

The witnesses in the conclusion are `B.reverse` and `Ar i = A i.rev`.
They have the required positive sizes and sum, and inherit the three block
properties from the original factors. The published theorem
`squareIntegrableBlockInductionIrreducibility.{uF,uV} F T` proves
irreducibility of their actual normalized upper product `I`.

To construct the final isomorphism, the factorization equivalence is pulled
back along the opposite Levi projection. `twistEquiv` retains the opposite
half-modulus character and `Induction.smoothInducedEquiv` induces this
equivalence. The published `Langlands.glOppositeProductReversal` identifies
the resulting opposite product with `I`, using the reversed ordered factors.
Composing these equivalences with the support injection yields an actual
injective intertwining map `k : π → I`. The input irreducibility gives a
nonzero vector, so injectivity shows that `k` is nonzero. Irreducibility of
both representations and
`Representation.IsIrreducible.bijective_or_eq_zero` make `k` bijective.
Finally, `k.ofBijective` and `SmoothRep.mkIso` give the required category
isomorphism, in the direction from the input representation to `I`.

The product in this proof is the unchanged
`T.normalizedProductInductionFunctor`: upper block parabolic, positive
half-modulus covariance and right translation. Opposite induction occurs
only in the support construction and is compared by the proved reversal
equivalence. The analytic predicates remain the actual all-Haar coefficient
conditions on the full central quotients: `L^(2+ε)` for temperedness and
`L²` for square-integrability. `IsUnitarizable` retains existence of a positive
definite invariant Hermitian form.

This module is an internal composition of published results. Its mathematical
inputs and their proof explanations are:

| Published proof pair | Role in this proof |
| --- | --- |
| [Tempered support](TemperedSupportProof.md) | Supplies the actual irreducible all-Haar square-integrable Levi support and injective opposite-induction map. |
| [Admissible Levi factorization](../CuspidalSupport/LeviAdmissibleFactorizationProof.md) | Supplies actual irreducible admissible block factors and their tensor equivalence. |
| [Block tensor square-integrability](BlockTensorSquareIntegrableProof.md) | Reflects the Levi analytic predicate to the factors. |
| [Square-integrable unitarity](SquareIntegrableUnitarityProof.md) | Supplies actual invariant positive forms on those factors. |
| [Opposite product reversal](../Induction/OppositeProductReversalProof.md) | Compares the opposite product with the upper product of reversed blocks. |
| [Square-integrable induction irreducibility](SquareIntegrableInductionIrreducibilityProof.md) | Makes that upper product irreducible. |

The original assertion is Kudla 1994, Proposition 2.2.1, printed p.373,
following the analytic tempered definition on p.372, as documented in the
[unchanged statement pair](TemperedBlockStatement.md). The implemented route
uses the published analytic support proof and its Silberger weak-critical
support route; it does not infer exhaustion from Jacquet 1977, which has no
such assertion. The factor form theorem implements the coefficient-integral
argument of Casselman 1995, Proposition 2.5.4, p.29, with the Library's
conjugate-first Hermitian convention. The induction irreducibility input uses
the published analytic segment classification, nonlinkage and product
criterion. These cited proof pairs retain their own source comparisons and
implemented lower proofs. No source assertion is used as a Lean hypothesis.

The local composition neither assumes the parent tempered unitarity and
genericity theorem nor uses regular Langlands exhaustion, equal-exponent
grouping, or tempered block uniqueness. It constructs every witness of the
existing target without changing the statement pair or any of its imports.
