# Conditional tempered special-segment refinement

Authors: Worker 627 (construction and proof), Worker 825 (submission).

The Lean file is Worker 627's shared draft revision 2 of task
`39db484c-8283-490b-88be-272c757a8723`, reused without change. It imports the
published statement module instead of the draft's copy. Worker 825 added this
authorship paragraph and repeated the import-closure audit below at Library
base `b01da032d726d4650356a35c834df86b9076165d`.

`temperedSpecialSegmentRefinementAssembly` implements the implication
`TemperedSpecialSegmentRefinementAssembly.{uF,uV} F T`. It keeps all four
inputs explicit: `TemperedBlockExhaustion`,
`SegmentEssentialSquareIntegrableClassification`,
`LinkedSegmentHeadExponentComparison`, and
`Parabolic.OrderedProductRegrouping`, with regrouping specialized to the
saturated carrier universe `max uF uV`. It does not prove any of these four
hypotheses or the unconditional refinement target. The outer prime, field,
and topological data, and the independent universe parameters, are preserved.

For one irreducible tempered parent block, `refineTemperedBlock` applies
exhaustion to the untwisted block. The resulting factors are irreducible,
square-integrable, and unitarizable before the real twist. Each twisted factor
is irreducible and essentially square-integrable, so the classification input
gives an actual segment and its strong segment-head relation. The resulting
degree equalities are used to construct the inner `SegmentProductDatum` and
transport the factor representations to its exact segment degrees.

`twistedUnitaryExponent` starts with exponent zero and the invariant positive
form on the untwisted factor. Its published `UnitaryExponentData.shift`
construction then gives an exponent witness for the real twist with exponent
exactly the parent exponent. `rankTransportUnitaryExponent` preserves that
exponent under the degree equality. No uniqueness theorem for exponents and
no assertion that arbitrary real twists remain square-integrable or unitary
is used. `TemperedBlockSegmentData` stores these witnesses, their exact exponent
equalities, the strong heads, and the isomorphism to the twisted parent block.

`commonRealTwistProductIso` specializes the published
`twistedProductCharacterTwist` proof to the smooth real norm character.
`segmentFactorZeroIso` removes the auxiliary exponent-zero twists using actual
smooth categorical isomorphisms. Together with the exhausted parent
isomorphism and the same-length `productRankIso`, this constructs the inner
induced-object isomorphism.

`flattenSegmentData` labels the output segments and blocks through the inverse
of `BlockShape.flattenBlockEquiv`. Its shape is definitionally the consecutive
flattening of the inner shapes, so the actual total degree equality is the
flattened shape's sum equality. The published lexicographic comparison for
that equivalence shows that an earlier output block's parent is no later than
the later block's parent. If its segment preceded the later segment, the strict
clause of the comparison input would force its exponent to be strictly smaller.
The stored equalities identify these exponents with the parent exponents,
contradicting the input datum's decreasing exponents, including equal parent
indices. This proves `IsPrecedenceOrdered` while retaining every strong head.

`flattenSegmentData_inducedIso` applies the regrouping hypothesis with the exact
published consecutive-coordinate identity. `reindexRankIso` removes the
dependent label and rank transports in each inner family; outer functoriality
then supplies the flattened-to-nested isomorphism. Composing it with the inner
isomorphisms proves that the actual output induced object is isomorphic to the
original tempered datum's standard module.

This is internal composition of existing Library definitions and constructions.
It imports no downstream quotient coverage or multisegment, square-integrable,
or regular exhaustion proof. The only proof imports beyond the named
interfaces are `TwistedProductCharacterTwistProof` and
`CuspidalSupport.MinimalJacquetProof`; their published lower-level constructions
supply common twists and finite ordered flattening, respectively. Their project
import closure has 83 modules, and this module's full project closure has 101.
Neither contains, imports or names a proof of `OrderedMultisegmentQuotientExhaustion`,
`MultisegmentHeadExhaustion`, `SquareIntegrableLanglandsExhaustion` or
`GLRegularLanglandsExhaustionStatement`. No new
literature theorem or analytic classification claim is made.
