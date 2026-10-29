# Upper discrete-series quotient support for tempered product Levis

Author: Worker 470.

`Langlands.glTemperedLeviUpperSupport` proves exactly the closed proposition
[`GLTemperedLeviUpperSupportStatement`](TemperedLeviUpperSupportStatement.md).
For every supplied prime, p-adic field, compatible topology, positive rank,
and ordered block shape `B`, an irreducible representation
`π : Rep.{uV} ℂ (B.Levi F.Carrier)` that is analytically tempered modulo the
full product Levi center is a quotient of upper normalized refined induction
from irreducible square-integrable data on a flattened refinement.

The field universe `uF` and original carrier universe `uV` are independent.
The resulting support representation has carrier in `Type (max uF uV)`,
while the target of the actual surjective intertwiner remains the given
representation on its original carrier in `Type uV`. The theorem has no
additional hypotheses.

## Implemented proof

The helper `TemperedLeviUpperSupportProof.ambientUpperQuotient` first applies
the closed
[`glTemperedDiscreteSeriesSupport`](TemperedSupportProof.md)
to an irreducible tempered GL block. This supplies an irreducible support
representation in the same carrier universe, its square-integrability for
every Borel Haar measure on the full Levi central quotient, and an actual
embedding into normalized opposite induction.

The helper chooses a Borel Haar measure on that quotient using
`exists_isHaarMeasure_leviCentralQuotient`. The closed
[`glTemperedDiscreteSeriesOppositeToUpper`](DiscreteSeriesOppositeToUpperProof.md)
gives an upper-induction embedding for the identical inducing representation.
The theorem
[`isSemisimple_bothInduced_of_squareIntegrable`](DiscreteSeriesInductionForms.md)
supplies semisimplicity of this upper induction from the support's
irreducibility and square-integrability for the chosen measure.
`semisimpleRetraction` then splits the upper embedding. Evaluating the
retraction identity on a vector proves that the retraction is surjective.
The support representation and its all-measure analytic property are retained.

The main proof applies the closed
[`glWholeLeviTemperedFactorization`](WholeLeviTemperedFactorizationProof.md)
to the given `π`. It obtains irreducible admissible tempered GL block
factors `X i`, together with an actual representation equivalence from `π`
to their external tensor product. Applying `ambientUpperQuotient` to each
block chooses the inner block shapes `Q i`, square-integrable inner-Levi
representations, and surjective block intertwiners. Their admissibility
bundles them as smooth representations for the refined-induction comparison.

The helper `existsFlattenedSquareIntegrable` constructs the actual
flattened support representation. It uses
`CuspidalSupport.padicLeviAdmissibleFactorization` to factor each
square-integrable inner-Levi representation into irreducible admissible
GL factors. The analytic equivalence
[`glBlockTensorSquareIntegrable`](BlockTensorSquareIntegrableProof.md)
reflects square-integrability to those factors after transport along the
factorization equivalence. Reindexing the factors by
`flattenBlockEquiv.symm` gives a family on the flattened block shape.
Admissible Schur and `FiniteTensor.isIrreducible_external` prove
irreducibility of its tensor representation. The same analytic equivalence
proves square-integrability modulo the full flattened Levi center.

`reindexRankEquiv` handles the dependent rank transport by eliminating an
equality of indices. This transport,
`FiniteTensor.flattenedTensorRegroupEquiv`, and the actual factorization
equivalences identify the flattened support with the external tensor of the
inner-Levi data, pulled back along `flattenedLeviProductEquiv`.

`ProductLeviCuspidalJacquetAssembly.inducingEquiv` pulls that equivalence
back to the actual refined subgroup, and
`normalizedRefinedInducedCongr` transports it through normalized induction.
The closed
[`Parabolic.refinedInductionTensor`](../Parabolic/RefinedInductionTensorProof.md)
then identifies this induction with the external tensor product of the
upper block inductions. The map `FiniteTensor.externalMap` formed from the
block quotient maps is surjective by
[`FiniteTensor.externalMapSurjectivity`](../Tensor/ExternalMapSurjectivityProof.md).
Composing these maps with the inverse of the original factorization
equivalence gives a surjective intertwiner onto the original `π`.

Finally, `universeLiftRepresentation` raises only the flattened support
carrier from `Type uV` to `Type (max uF uV)`. Its representation equivalence
preserves irreducibility and transports square-integrability for every
Borel Haar measure on the same full-center quotient. Pulling the inverse
equivalence back along `flattenedLeviEquiv` and transporting through
normalized refined induction gives the final induced equivalence. Its
composition with the preceding quotient is the required map from
`RelativeRegularComparison.middleInduced T B Q σ` onto `π`.

All analytic transports use actual representation equivalences. The target's
full-center, all-Haar predicates and its actual upper normalized induction
remain unchanged, including the supplied topology, positive-half-modulus
covariance, right translation, and residue-normalized absolute value.
The proof derives the tensor presentation from the original hypotheses.
Ambient support and the same-data comparison are imported closed theorems.

## Provenance and scope

This is a derived product-Levi construction using the named Library proofs.
The source motivation is the initial discrete-series quotient-support step
in A. J. Silberger, *The Langlands Quotient Theorem for p-adic Groups*
(1978), Proposition 5.1 proof setup, printed p.99. The source is registered as
`provided-5423f8a28c0b7ad5a7f9a07a3d55d399d5162a798fecd70bf11a5d75fa8b9354`,
SHA-256
`4f437d7ee21c65e43ede0a34b9a6b274cf4d947c23ad7637976bd38fd72fdac5`.
Printed pp.96–97 fix normalized induction and recall exactness, stages,
and the subrepresentation/opposite-quotient correspondence. Worker 470
read pp.96–99 directly and checked the opposite notation and quotient setup
in page images.

The ambient opposite-support route comes from Silberger,
*Introduction to Harmonic Analysis on Reductive p-adic Groups* (1979),
Corollary 4.5.11, printed pp.189–190, registered as
`silberger-1979-harmonic-analysis`, SHA-256
`b9432812bb48ce0bcd3975144baa6b3cca99bcaaf0d33d785ce68e94e02854fc`.
Worker 470 read those pages and checked the formulas in images.
That corollary supplies an opposite-induction embedding. The implemented
proof obtains the upper quotient through the published same-data comparison
and semisimple retraction described above. No source-specific errata file
was found in the project or Library notes when checking these passages.

The sources do not literally state the present flattened-product formula;
the analytic factorization, regrouping, subgroup and induction transports
are the formal derivation. Their imported paired explanations describe
the underlying results. The constituent restriction recorded in
[`silberger-lemma53-scope.md`](../../../notes/jacquet/silberger-lemma53-scope.md)
is preserved. This proof uses no joint-support theorem, downstream
square-integrable Langlands classification, regular-data uniqueness,
or unrestricted multiplicity comparison.
