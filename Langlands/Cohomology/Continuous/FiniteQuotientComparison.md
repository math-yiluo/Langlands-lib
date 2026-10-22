# The canonical finite-quotient comparison map

Author: Worker 22. This definition contribution imports the published
`CochainComparisonLawsProof` and constructs the canonical colimit comparison.

For a topological group `G` and `A : DiscreteModule k G`, this module constructs
the canonical map `Langlands.Continuous.finiteQuotientComparison A q` from
the actual colimit of `H^q(G/N,A^N)` to the underlying module of Mathlib's
actual `continuousCohomology q A.toTopRep`. It uses the actual inflation
diagram defined in `FiniteQuotientSystem`. The ring, group and coefficient
carrier retain arbitrary common universe `u`; `q` is any natural number.
The discrete-module data includes joint continuity of the action.

The map itself requires no compactness. Its open normal quotients are
discrete; compactness of `G` implies that they are finite, as proved in
`FiniteQuotientSystem`. Invertibility of this new colimit comparison is not
asserted or assumed in this definition contribution.

## Finite-stage maps and their certificates

`underlyingContinuousCochains` is the actual nested homogeneous cochain
complex with topology forgotten. The published `nestedEval_injective`
uses induction and extensionality to detect equality. Evaluation on each tuple generator therefore
detects a homogeneous cochain, and the standard-to-inhomogeneous complex
isomorphism preserves that injectivity. This proves the degreewise
injectivity, and hence the categorical monomorphism property, of the
canonical cochain comparison. It does not assert injectivity on cohomology.

`ordinaryInflationCochains` uses the actual quotient homomorphism
`G → G/N` and the inclusion of `N`-invariants into the original coefficients.
For the discrete quotient group, the separately proved canonical cochain
comparison is invertible. `finiteStageCochainMap` composes its inverse with
the existing continuous cochain map for quotient projection and inclusion
of fixed coefficients.

Naturality of the canonical comparison shows that composing this map with
the comparison for `G` gives precisely `ordinaryInflationCochains`.
The converse composition formula at the finite stage is cancellation of
the proved discrete comparison isomorphism.

For `M ≤ N`, ordinary inflation through `G/M → G/N` followed by the
finite-stage map for `M` equals the finite-stage map for `N`.
The proof composes both sides with the injective canonical cochain
comparison, uses its finite-stage formula, and then uses the genuine
composition law for Mathlib's ordinary cochain maps. The quotient and
coefficient maps agree by extensionality.
This proves the actual cocone certificate for `finiteStageCochainCocone`.

## Homology and the colimit map

Applying the actual degree-`q` homology functor to the cochain cocone gives
`finiteStageHomologyCocone` on the published finite-quotient cohomology
diagram. Its vertex is homology of the forgotten continuous complex.
`finiteQuotientComparison` first uses `Limits.colimit.desc` for this
cocone, then the actual homology-preservation isomorphism of the forgetful
functor to reach the underlying module of continuous cohomology.
No colimit equivalence or exactness property is supplied as a hypothesis.

`finiteStageToContinuous` is the same homology map at a single stage,
followed by the homology-preservation map. The colimit structural map
followed by `finiteQuotientComparison` equals this finite-stage map by
the universal property. The cochain refinement equality induces its
cohomology refinement equality by functoriality.

Naturality of the forgetful homology isomorphism proves that the map at
each stage is exactly inverse discrete cohomology comparison followed by
the existing `ContinuousCohomology.map` for quotient inflation.
This is recorded both as a composition identity and as
`finiteStageToContinuous_eq_inflation`. These are intrinsic descriptions
of the constructed map, not an identification of the source and target
cohomology groups by definition.

## Dependencies and provenance

The imports are `Langlands.Cohomology.Continuous.FiniteQuotientSystem`,
`Langlands.Cohomology.Continuous.CochainComparisonLawsProof`, and
Mathlib's homological-complex limits module.
The finite-quotient system and canonical comparison definitions were
independently reviewed and published at Library commit
`30ceb5a0d89d8094c1663fc19f35416519b9a125`.
The comparison-laws statement was published at Library commit
`6473a6d8b91ebfaf6d7cedffc41570c3e9edaa27`, and its exact proof was
published at `22b4f024e0d4218752e970d09329d1799f6d81d1`. Their current
Library declarations were verified before submission. The discrete
isomorphism theorems are installed as local instances in this module.

The construction follows Serre, *Local Fields*, Greenberg translation,
Springer (1979), VII Section 5, printed pages 115–117 / PDF pages 121–123
(compatible maps and inflation), and X Section 3, printed pages 154–155 /
PDF pages 160–161 (the inflation direct limit and continuous cochains).
The nested-model comparison and its cancellation arguments are derived
implementation work. Literature ID `serre-1979-local-fields`, PDF SHA-256
`109b461d42915da70771c70c4b551a363fc1f33412331ae2671c5c85be433112`.

Environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`, version 1:
Lean 4.34.0 (`293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`);
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
The colimit comparison's isomorphism theorem and continuous transfer
remain separate statement, proof and publication obligations.
