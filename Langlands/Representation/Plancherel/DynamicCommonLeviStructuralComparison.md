# Structural comparison with actual common-Levi data

This is an internal, derived adapter for the actual standard integrals and fixed
compact pictures in Waldspurger, *La formule de Plancherel*, IV.1, printed
pp.276–278 (PDF pp.42–44). It constructs structural comparison maps; it does not
prove IV.1.1 or the remaining presentation-to-existence reduction.

The namespace is
`Langlands.Plancherel.DynamicCommonLeviStructuralComparison`. Its parameter and
scheme maps are those constructed in `DynamicCommonLeviPresentationComparison`.
No group, representation, family or rationality equivalence is assumed.

## Literal subgroup maps and normalization

For equal literal parabolic, Levi and radical subgroups, the generic
`compactPictureComparisonOfEq` and `leviInductionComparisonOfEq` preserve the
underlying ambient function and its original inducing vector space. Their
evaluation lemmas retain every compact or ambient argument. The latter map is
between positive Levi-normalized inductions. `projectionComparisonOfEq` proves
compatibility of the semidirect projections, and `halfCharacterComparisonOfEq`
proves compatibility of the actual positive Haar half characters. The proofs
substitute the subgroup equalities; semidirect decompositions and closedness
witnesses are propositions, so proof irrelevance identifies the resulting
normalization data. No additional modulus comparison is postulated.

For an arbitrary nonarchimedean local field and an affine locally finite type
ambient group scheme, `Realizes χ ψ p l n` supplies all-test equalities of the
presented parabolic, Levi and radical with the dynamic functors. A cocharacter
centralizer equality `hψ` gives the literal common dynamic Levi. The maps
`compactPictureComparison` and `leviInductionComparison` specialize the generic
constructions using the proved point subgroup equalities. The supplied source
semidirect decomposition `h` and source radical closedness `hU` are explicit.
`presentationRepresentation` pulls back the canonical common-Levi representation
by the identity on ambient Levi elements, keeping its carrier universe independent
of the field universe.

A complete `ParabolicRootPresentation r` is used for character comparison.
`characterComparison_parameterTransport` and `twistedRepresentation_eq` identify
the actual scalar and linear actions for the full rational-character norm
families. Their index types may differ. `unramifiedInductionComparison` then
compares the varying induced representations at corresponding parameters; its
evaluation lemma is identity on every ambient group argument.

`compactRestriction_comparison` proves the square between the source
`unramifiedLeviInductionCompactEquiv`, the fixed compact-section comparison,
`unramifiedInductionComparison` and the actual `compactEquiv`. Its explicit
inputs are source radical unimodularity, parabolic closedness, compactness of
`K`, the source factorization and projection continuity, connected reductivity
of `G`, and the dynamic factorization at that same `K`. The proof compares
pointwise evaluations and uses the restriction evaluation lemmas. The radical
unimodularity in this square is only an input of this structural map; no
existence target is weakened to assume an analytic conclusion.

## Intersections, quotients and the source scale

`intersectionComparisonOfEq` is identity on the doubly wrapped ambient element.
`quotientComparisonOfEq` is the induced homeomorphism on the actual left coset
spaces, as its formula on quotient representatives shows. All measures in this
section use the Borel measurable structures of their indicated topologies.

`subgroupMeasureOfEq`, `intersectionMeasureOfEq` and `quotientMeasureOfEq` pull
back specified measures by mapping along the inverse of the constructed
homeomorphism. The three `_map` theorems prove that mapping forward recovers
the original measures exactly. The subgroup and intersection constructions
preserve Haar measure, regularity and right invariance.
`quotientMeasureOfEq_isCompatible` transports every field of complex Weil
compatibility, including nonzero regular quotient measure, right invariance,
average integrability and the integral formula. After equality substitution the
proof is `Measure.map_id`, with the right-invariant instance supplied explicitly.

For two realizations, `presentationRadicalHaar`,
`presentationIntersectionHaar` and `presentationQuotientMeasure` pull back
respectively `radicalHaar ψ' K hK`, `pairIntersectionHaar K hK ψ ψ'` and
`pairQuotientMeasure K hK ψ ψ'`. Their forward image theorems show exact
preservation of the original source scale. The first two measures retain the
three stated measure properties, and
`presentationQuotientMeasure_isCompatible` proves compatibility of exactly
these three measures. The source radical representations may differ from the
dynamic schemes: only the literal point equalities enter the maps. No arbitrary
choice of an unrelated quotient measure is used.

## Remaining boundary

These results provide actual structural maps and a proved compact restriction
square. The remaining task is to derive the actual rational starting-region
existence assertion from the complete presentation-level
`ConditionalParabolicIntertwiningStatement`, with both compatible presentations
and its auxiliary opposite presentation. That requires assembling the scalar
weak-integral/domain comparison, admissibility and finite-length transport,
and restriction of the saturated rationality region through the constructed
character and compact maps. This module does not claim that assembly is proved.
No convergence, rationality, continuation, invertibility or unitary regularity
assertion is a permanent structural hypothesis. All statements retain arbitrary
characteristic, nonsplit groups and independent representation-carrier universes.
