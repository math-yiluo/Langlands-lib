# Terminal supports for derivatives of supplied head products

Author: Worker 357.

This internal specialization constructs actual factor-derivative constituent
data for an irreducible subquotient of a derivative of a supplied special-head
product, or of a supplied subquotient of that product. At every original
segment label, the underlying set of a chosen supercuspidal support is the
support of an optional terminal truncation. The chosen support multisets sum
to a supercuspidal support of the supplied derivative constituent.

The entry constructor is
`Langlands.Classification.segmentHeadProductTerminalSupportDataOfSubquotient`.
The same focused unit provides its whole-product specialization and two
existential projections to terminal truncations and their support union.
The full product irreducibility criterion is not established here.

## Parameters and precise scope

Fix arbitrary `p : ℕ` with `Fact p.Prime`, a supplied
`F : PadicField.{uF} p`, a supplied `T : F.TopologicalData`, and a supplied
unitary additive character `ψ` for `T.topology`. No nontrivial-character
hypothesis is added. The universes `uF` and `uV` are independent.

Let `0 < n`, `k ≤ n`, and `d : T.SegmentProductDatum.{uV,uF} n`, with
`hd : d.HasSegmentHeads`. This is the pointwise supplied special-head
relation on the actual block family of `d`; it is not a relation to the
socles of the increasing segment inductions.

The source `Q` is an actual smooth complex representation of `GL_n(F)`
with `SmoothRep.IsSubquotient Q d.induced`. The supplied `D` is an actual
irreducible smooth complex representation of `GL_(n-k)(F)`, with an actual
subquotient occurrence in `((generalLinearDerivative T ψ n k hk).obj Q)`.
Subquotient relations are written constituent first. There is no
irreducibility or finite-length premise on `Q`.

All actual representation carriers have universe `max uF uV`.
All cuspidal support multisets and segments retain the original base
universe `uV`. No lifting or resizing of the supplied field or support data
occurs. The original labels `Fin d.length`, their order, and repeated
segments are retained. Source rank is positive; derivative orders zero and
top rank are included. Residual ranks of `D` and extracted factors can be
zero. No nonlinkage or distinctness premise is used.

## Predicate and returned data

`TerminalSupportPredicate T Δ k s` means precisely

```text
∃ A : Option (T.Segment),
  Segment.IsTerminalTruncation A Δ ∧
  {ρ | ρ ∈ s} = Segment.optionalSupport A.
```

The argument `k` is deliberately unused by this predicate. `none` has empty
optional support; a present segment has its actual support and the terminal
endpoint condition of the published truncation definition. The predicate
contains no derivative identification or derivative-order formula.

The entry constructor returns the published
`ProductDerivativeSupport.SupportData T ψ d.shape d.blocks D`
with predicates `fun i => TerminalSupportPredicate T (d.segments i)`.
For each original label this stores a feasible derivative order, an actual
irreducible constituent of that derivative of the original block, its actual
occurrence, a supercuspidal support multiset, and the stated terminal-support
predicate. The chosen orders sum to `k`; the chosen support multisets sum to
a supercuspidal support of `D`. These order and support fields come from the
general constructor, not from a formula identifying individual derivatives.

`segmentHeadProductTerminalSupportData` takes `Q = d.induced` with its
reflexive actual subquotient occurrence. It returns the same data for a
supplied constituent of the derivative of the whole product.

`segmentHeadProductTerminalTruncationSupportOfSubquotient` projects the
constructor to functions `A` and `s` on `Fin d.length`, satisfying

```text
∀ i, Segment.IsTerminalTruncation (A i) (d.segments i),
∀ i, {ρ | ρ ∈ s i} = Segment.optionalSupport (A i),
T.IsSupercuspidalSupport D (∑ i, s i).
```

`segmentHeadProductTerminalTruncationUnionOfSubquotient` returns a single
support multiset `s` of `D` and optional terminal truncations `A`, with

```text
{ρ | ρ ∈ s} = ⋃ i, Segment.optionalSupport (A i).
```

The support assertion is about an actual multiset. The displayed set
identity forgets multiplicities; it does not assert that a factor's support
multiset equals a segment's content multiset. No derivative irreducibility,
truncated-head identification, multiplicity formula, or product
irreducibility is asserted.

## Implemented construction and internal provenance

This pair translates no new external assertion. Its provenance is internal
and its source list is empty. It composes four published inputs.

| Direct import after `Langlands.Representation.` | Use |
| --- | --- |
| `Derivative.ProductDerivativeSupportAggregation` | General actual original-label support data, including the source-subquotient version |
| `Derivative.GeneralLinearDerivativeFiniteLengthProof` | Finite length of each derivative of an actual finite-length supplied block |
| `Classification.SegmentHeadDerivativeSupportTruncationProof` | Only the final independently proved support-only terminal-truncation theorem |
| `Classification.SegmentHeadProductFiniteness` | Supplied-head finiteness infrastructure |

Apply `ProductDerivativeSupport.supportDataOfSubquotient` to the original
block shape, block family, `Q` and `D`. For each original block its supplied
head relation gives irreducibility, hence finite length. Apply
`generalLinearDerivativeFiniteLength` to obtain the exact finite-length
premise for every feasible derivative of that block. It is instantiated at
carrier universe `max uF uV`, without changing the support universe.

For each actual irreducible subquotient `E` of such a derivative, apply only
`Langlands.Classification.segmentHeadDerivativeSupportTruncation` at the
original `uF,uV`, that block, segment and occurrence. Its support multiset,
optional terminal truncation and support-set equality give exactly the
predicate and actual support premise of the general constructor. The
constructor then supplies all original-label data, order sum and support
sum. No stronger result inside the individual support proof is invoked.

The first existential projection uses classical choice separately at each
original label to select the optional truncation from the stored predicate.
Its support family and final support sum are the fields of the constructed
data. The union projection uses `Multiset.mem_sum`, membership in the
universal finite index set, and the per-label set equalities. Extensionality
then proves that the underlying set of the summed multiset is the indexed
union. This uses no support-uniqueness theorem.

## Dependency and proof-route audit

At Library base `9d1720cbedcfd184cf48bf36249fc3029583cafa`, the recursive
inventory contains 1248 project modules including this entry and 320 directly
named external import roots. All 1247 inherited Lean/Markdown pairs are
byte-identical to that Library; all have nonempty paired Markdown. There are
no missing project imports. Every inherited pair matches both fingerprints
in the earlier audited general product-support, individual support-only or
individual/product-duality inventories. There is no changed inherited pair
or unmatched inherited module. The complete module inventory is below;
external roots are listed directly, without claiming a separate recursive
traversal of Mathlib.

The general product-support route uses actual general Leibniz filtrations,
finite-filtration constituent extraction, finite-length product filtrations,
ordered first/tail induction comparisons and general support addition. Its
source-subquotient projection uses proved derivative exactness and actual
subquotient transitivity. Its full paired proof explanation and dependency
audit are in `ProductDerivativeSupportAggregation.md`. That constructor is
independently accepted and published, and its current paired bytes equal the
reviewed frozen pair.

The general derivative finite-length route uses induction on composition
length, an actual cuspidal-product embedding for a simple input, exactness,
and the conditional product derivative finite-length theorem. The published
individual support-only proof uses its separately permitted general
derivative foundations and individual-head constructions. Its audited route
retains the support-only conclusion. The length-two base uses permitted
adjacent reducibility and a stronger intermediate step, within that base
only. This consumer uses neither intermediate step nor any separate
adjacent/nonadjacent product conclusion.

The broad scan has no unclassified exclusion hits. Hits for
`SegmentHeadDerivative` designate the permitted support-only statement,
proof and helpers, and this consumer's application of the final theorem.
Hits for the nonadjacent two-supercuspidal theorem occur only inside the
published adjacent-reducibility closure used in that support proof's
length-two base. Broader `TwoSupercuspidalProductStructureStatement` imports
are proposition interfaces; the actual `TwoSupercuspidalProductStructureProof`
is absent. The completed route audit supplements the name scan: proposition
definitions and imported statements are not used as proved inputs.

The trusted operator rulings
[bd71b9185aab5d6eafffb7891bd3a3ca](/home/taskhub/pilot/correspondence/bd71b9185aab5d6eafffb7891bd3a3ca.md),
[0edda6122ce65ed7ac51603c37473920](/home/taskhub/pilot/correspondence/0edda6122ce65ed7ac51603c37473920.md),
[30144f6f9b59540b88b6d4c1517892d9](/home/taskhub/pilot/correspondence/30144f6f9b59540b88b6d4c1517892d9.md),
and [ed80148e21e7523abfc048f455e98eb0](/home/taskhub/pilot/correspondence/ed80148e21e7523abfc048f455e98eb0.md)
were read in full. They permit independently proved general derivative
theory, the newly proved exactly support-only bound, and its restricted
length-two intermediate step. The reducibility permissions
[2b33898bdd0a5ff1b9031be5155a06f0](/home/taskhub/pilot/correspondence/2b33898bdd0a5ff1b9031be5155a06f0.md)
and [ca18fd5005bf5e12a3f7cade18dca865](/home/taskhub/pilot/correspondence/ca18fd5005bf5e12a3f7cade18dca865.md)
were also read in full. They are confined to that support proof's base case.
This constructor invokes only its final support theorem, never `core_mid`,
`core`, their at-most-one-simple-factor consequence or a replacement segment
formula. The support proof's published Markdown records the detailed lower
route and the same restrictions.

The closure contains no Ze80 3.5/9.6 formula or proof successor, segment-socle
derivative formula, full segment/head/socle/Jacquet formula, or downstream
classification proof used as a premise. It is independent of parent
`GenericSegmentProductUniqueness`, multisegment exhaustion, ordered
strong-head existence, quotient coverage, ordered conversion, tempered
uniqueness, square-integrable classification and exhaustion, regular
exhaustion, and the full host criterion in either direction. The
segment-socle part of task `8e5b4563` is excluded. No derivative
irreducibility, truncated-head identification, multiplicity result or
stronger support-proof intermediate result is added as a consumer input.
The exact proof route and all inherited fingerprints have been reconciled;
there are no holes, new axioms, prohibited native syntax or missing pairs.

## Validation

The private and ordinary entry modules compiled at this base through the
approved Lean service with zero errors and zero warnings. The ordinary
selected-constructor inspection used a Lake build, reports exactly the
independent level parameters `uF,uV`, and reports only `propext`,
`Classical.choice` and `Quot.sound`. Compilation and this author audit do
not establish independent semantic acceptance.

## Complete project import inventory

- `Langlands.Algebra.CommutingDimensionHelpers`
- `Langlands.Algebra.CommutingDimensionNilpotent`
- `Langlands.Algebra.CommutingDimensionNumerics`
- `Langlands.Algebra.CommutingDimensionPrimary`
- `Langlands.Algebra.CommutingDimensionRecurrence`
- `Langlands.Algebra.MultisetOfFn`
- `Langlands.Algebra.SandwichDimensionBoundProof`
- `Langlands.Algebra.SandwichDimensionBoundStatement`
- `Langlands.Algebra.SeparatedMatrixRepresentations`
- `Langlands.Analysis.Local.CompactOpenCoverUnimodularityProof`
- `Langlands.Analysis.Local.CompactOpenCoverUnimodularityStatement`
- `Langlands.Analysis.Local.ModularCompactAverage`
- `Langlands.Analysis.Local.QuotientAutomorphismProof`
- `Langlands.Analysis.Local.QuotientAutomorphismStatement`
- `Langlands.Analysis.Local.QuotientAverageReal`
- `Langlands.Analysis.Local.QuotientAveragingKernel`
- `Langlands.Analysis.Local.QuotientComplex`
- `Langlands.Analysis.Local.QuotientFunctional`
- `Langlands.Analysis.Local.QuotientMass`
- `Langlands.Analysis.Local.QuotientMeasure`
- `Langlands.Analysis.Local.QuotientMeasureExistence`
- `Langlands.Analysis.Local.QuotientMeasureExistenceStatement`
- `Langlands.Analysis.Local.QuotientMeasurePrerequisites`
- `Langlands.Analysis.Local.QuotientPositiveLifting`
- `Langlands.Analysis.Local.QuotientTopology`
- `Langlands.Analysis.Local.QuotientTranslation`
- `Langlands.Analysis.Local.SplitKernelQuotient`
- `Langlands.ClassFieldTheory.Local.Completion`
- `Langlands.ClassFieldTheory.Local.FiniteArtin`
- `Langlands.ClassFieldTheory.Local.Galois`
- `Langlands.ClassFieldTheory.Local.Norms`
- `Langlands.ClassFieldTheory.Local.ProfiniteReciprocityStatement`
- `Langlands.ClassFieldTheory.Local.ReciprocityRelations`
- `Langlands.ClassFieldTheory.Local.Transfer`
- `Langlands.ClassFieldTheory.Local.Units`
- `Langlands.ClassFieldTheory.Local.WeilAbelianization`
- `Langlands.ClassFieldTheory.Local.WeilReciprocityStatement`
- `Langlands.Combinatorics.RelationInversions`
- `Langlands.Correspondence.AutomorphicRelations`
- `Langlands.Correspondence.Domains`
- `Langlands.Correspondence.LocalConventions`
- `Langlands.Correspondence.OperationCompatibility`
- `Langlands.Correspondence.SupercuspidalRelations`
- `Langlands.Correspondence.UnramifiedNormalization`
- `Langlands.Galois.FiniteField.Comparison`
- `Langlands.Galois.FiniteField.ComparisonProof`
- `Langlands.Galois.FiniteField.Frobenius`
- `Langlands.Galois.Local.AbsoluteDefinitions`
- `Langlands.Galois.Local.AbsoluteProof`
- `Langlands.Galois.Local.AbsoluteStatement`
- `Langlands.Galois.Local.SpectralDefinitions`
- `Langlands.Galois.Local.SpectralProof`
- `Langlands.Galois.Local.SpectralStatement`
- `Langlands.Group.GL.AdjacentMergeShape`
- `Langlands.Group.GL.Basic`
- `Langlands.Group.GL.BlockContractionProof`
- `Langlands.Group.GL.BlockContractionStatement`
- `Langlands.Group.GL.BlockDeterminant`
- `Langlands.Group.GL.BlockIwahoriBasis`
- `Langlands.Group.GL.BlockIwahoriBasisStatement`
- `Langlands.Group.GL.BlockIwahoriDefinitions`
- `Langlands.Group.GL.BlockModulus`
- `Langlands.Group.GL.BlockModulusHaarProof`
- `Langlands.Group.GL.BlockModulusHaarStatement`
- `Langlands.Group.GL.BlockScalarCenter`
- `Langlands.Group.GL.BlockUnipotent`
- `Langlands.Group.GL.BlockUnipotentCoordinates`
- `Langlands.Group.GL.BlockUnipotentHaarProof`
- `Langlands.Group.GL.BlockUnipotentHaarStatement`
- `Langlands.Group.GL.Blocks`
- `Langlands.Group.GL.CartanProof`
- `Langlands.Group.GL.CartanStatement`
- `Langlands.Group.GL.CentralQuotientTopologyProof`
- `Langlands.Group.GL.CentralQuotientTopologyStatement`
- `Langlands.Group.GL.CompactOpen`
- `Langlands.Group.GL.CountabilityProof`
- `Langlands.Group.GL.CountabilityStatement`
- `Langlands.Group.GL.DominantExponentGeneration`
- `Langlands.Group.GL.HeadTailBlocks`
- `Langlands.Group.GL.IntegralSubgroup`
- `Langlands.Group.GL.InverseTransposeIwahoriProof`
- `Langlands.Group.GL.InverseTransposeIwahoriStatement`
- `Langlands.Group.GL.Maps`
- `Langlands.Group.GL.Mirabolic`
- `Langlands.Group.GL.MirabolicMixedOrbitCoverageProof`
- `Langlands.Group.GL.MirabolicMixedOrbitCoverageStatement`
- `Langlands.Group.GL.MirabolicMixedOrbitData`
- `Langlands.Group.GL.MirabolicMixedOrbitRadicals`
- `Langlands.Group.GL.MirabolicMixedOrbitSectionCoefficients`
- `Langlands.Group.GL.MirabolicMixedOrbitSections`
- `Langlands.Group.GL.MirabolicMixedOrbitSpecializations`
- `Langlands.Group.GL.MirabolicMixedOrbitStages`
- `Langlands.Group.GL.MirabolicMixedProductSubgroups`
- `Langlands.Group.GL.MirabolicModularCharacterProof`
- `Langlands.Group.GL.MirabolicModularCharacterStatement`
- `Langlands.Group.GL.MirabolicModulusProof`
- `Langlands.Group.GL.MirabolicModulusStatement`
- `Langlands.Group.GL.MirabolicOppositeIntersection`
- `Langlands.Group.GL.MirabolicProjection`
- `Langlands.Group.GL.MirabolicRadical`
- `Langlands.Group.GL.NestedRefinement`
- `Langlands.Group.GL.Nonarchimedean`
- `Langlands.Group.GL.NonarchimedeanStatement`
- `Langlands.Group.GL.NormalizedCharacter`
- `Langlands.Group.GL.OneBlockShape`
- `Langlands.Group.GL.OppositeBlocks`
- `Langlands.Group.GL.Padic`
- `Langlands.Group.GL.PadicBlocks`
- `Langlands.Group.GL.PadicOppositeBlocks`
- `Langlands.Group.GL.PadicUpperUnipotent`
- `Langlands.Group.GL.ParabolicModularCharacter`
- `Langlands.Group.GL.PrincipalBlockFactorizationProof`
- `Langlands.Group.GL.PrincipalBlockFactorizationStatement`
- `Langlands.Group.GL.PrincipalLevelDominance`
- `Langlands.Group.GL.RankMaps`
- `Langlands.Group.GL.RankReindex`
- `Langlands.Group.GL.RefinementCoordinates`
- `Langlands.Group.GL.ReindexCongr`
- `Langlands.Group.GL.ReverseBlocks`
- `Langlands.Group.GL.SingleBlock`
- `Langlands.Group.GL.SingletonBlocks`
- `Langlands.Group.GL.Transvection`
- `Langlands.Group.GL.TriangularParabolic`
- `Langlands.Group.GL.UnramifiedCharacter`
- `Langlands.Group.GL.UpperBruhatBoundaryProof`
- `Langlands.Group.GL.UpperBruhatBoundaryStatement`
- `Langlands.Group.GL.UpperBruhatCells`
- `Langlands.Group.GL.UpperBruhatCoordinatesProof`
- `Langlands.Group.GL.UpperBruhatCoordinatesStatement`
- `Langlands.Group.GL.UpperBruhatEmbedding`
- `Langlands.Group.GL.UpperBruhatFiltration`
- `Langlands.Group.GL.UpperBruhatFiltrationGeometryProof`
- `Langlands.Group.GL.UpperBruhatFiltrationGeometryStatement`
- `Langlands.Group.GL.UpperBruhatLocalClosednessProof`
- `Langlands.Group.GL.UpperBruhatLocalClosednessStatement`
- `Langlands.Group.GL.UpperBruhatPivotProof`
- `Langlands.Group.GL.UpperBruhatPivotStatement`
- `Langlands.Group.GL.UpperBruhatProof`
- `Langlands.Group.GL.UpperBruhatRankProof`
- `Langlands.Group.GL.UpperBruhatRankStatement`
- `Langlands.Group.GL.UpperBruhatStatement`
- `Langlands.Group.GL.UpperBruhatTransposeProof`
- `Langlands.Group.GL.UpperBruhatTransposeStatement`
- `Langlands.Group.GL.UpperUnipotent`
- `Langlands.Group.GL.UpperUnipotentCompactContainmentProof`
- `Langlands.Group.GL.UpperUnipotentCompactContainmentStatement`
- `Langlands.Group.GL.UpperUnipotentFactorizationProof`
- `Langlands.Group.GL.UpperUnipotentFactorizationStatement`
- `Langlands.Group.HaarModulus`
- `Langlands.Group.LeftQuotient`
- `Langlands.HarmonicAnalysis.AlgebraicIntegral`
- `Langlands.HarmonicAnalysis.AlgebraicIntegrand`
- `Langlands.HarmonicAnalysis.Basic`
- `Langlands.HarmonicAnalysis.CharacterTransport`
- `Langlands.HarmonicAnalysis.Conductor`
- `Langlands.HarmonicAnalysis.Distribution.Basic`
- `Langlands.HarmonicAnalysis.Distribution.BruhatFiltrationVanishingProof`
- `Langlands.HarmonicAnalysis.Distribution.BruhatFiltrationVanishingStatement`
- `Langlands.HarmonicAnalysis.Distribution.CharacterAverage`
- `Langlands.HarmonicAnalysis.Distribution.CharacterAverageCovarianceProof`
- `Langlands.HarmonicAnalysis.Distribution.CharacterAverageCovarianceStatement`
- `Langlands.HarmonicAnalysis.Distribution.CharacterAverageFactorizationProof`
- `Langlands.HarmonicAnalysis.Distribution.CharacterAverageFactorizationStatement`
- `Langlands.HarmonicAnalysis.Distribution.CharacterAverageSurjectiveProof`
- `Langlands.HarmonicAnalysis.Distribution.CharacterAverageSurjectiveStatement`
- `Langlands.HarmonicAnalysis.Distribution.ClosedRestrictionProof`
- `Langlands.HarmonicAnalysis.Distribution.ClosedRestrictionStatement`
- `Langlands.HarmonicAnalysis.Distribution.ClosedSupportedDescentProof`
- `Langlands.HarmonicAnalysis.Distribution.ClosedSupportedDescentStatement`
- `Langlands.HarmonicAnalysis.Distribution.FiniteOrbitVanishingProof`
- `Langlands.HarmonicAnalysis.Distribution.FiniteOrbitVanishingStatement`
- `Langlands.HarmonicAnalysis.Distribution.GeneralLinear`
- `Langlands.HarmonicAnalysis.Distribution.HomogeneousPositivityProof`
- `Langlands.HarmonicAnalysis.Distribution.HomogeneousPositivityStatement`
- `Langlands.HarmonicAnalysis.Distribution.HomogeneousVanishingProof`
- `Langlands.HarmonicAnalysis.Distribution.HomogeneousVanishingStatement`
- `Langlands.HarmonicAnalysis.Distribution.LocalizationProof`
- `Langlands.HarmonicAnalysis.Distribution.LocalizationStatement`
- `Langlands.HarmonicAnalysis.Distribution.OpenRestrictionLocalityProof`
- `Langlands.HarmonicAnalysis.Distribution.OpenRestrictionLocalityStatement`
- `Langlands.HarmonicAnalysis.Distribution.Subspace`
- `Langlands.HarmonicAnalysis.Distribution.SupportedDescentCovarianceProof`
- `Langlands.HarmonicAnalysis.Distribution.SupportedDescentCovarianceStatement`
- `Langlands.HarmonicAnalysis.Distribution.SupportedRestriction`
- `Langlands.HarmonicAnalysis.Distribution.TransposeInvariantProof`
- `Langlands.HarmonicAnalysis.Distribution.TransposeInvariantStatement`
- `Langlands.HarmonicAnalysis.FiniteProductMeasureScaling`
- `Langlands.HarmonicAnalysis.HaarConjugacy`
- `Langlands.HarmonicAnalysis.PadicAdditiveConductorProof`
- `Langlands.HarmonicAnalysis.PadicHaarScalingStatement`
- `Langlands.HarmonicAnalysis.PadicLatticeTopology`
- `Langlands.HarmonicAnalysis.PadicRectangularHaarScalingProof`
- `Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof`
- `Langlands.HarmonicAnalysis.PadicUnitaryAdditiveCharacterExistsProof`
- `Langlands.HarmonicAnalysis.PadicUnitaryAdditiveCharacterExistsStatement`
- `Langlands.HarmonicAnalysis.RowFourier`
- `Langlands.HarmonicAnalysis.RowSchwartzAction`
- `Langlands.HarmonicAnalysis.RowTensorDecompositionProof`
- `Langlands.HarmonicAnalysis.RowTensorDecompositionStatement`
- `Langlands.HarmonicAnalysis.RowTestSmoothProof`
- `Langlands.HarmonicAnalysis.RowTestSmoothStatement`
- `Langlands.HarmonicAnalysis.SmoothWeakIntegral`
- `Langlands.HarmonicAnalysis.TriangularTranslationProof`
- `Langlands.HarmonicAnalysis.TriangularTranslationStatement`
- `Langlands.LinearAlgebra.CyclicQuotientPairingProof`
- `Langlands.LinearAlgebra.CyclicQuotientPairingStatement`
- `Langlands.LinearAlgebra.FiniteRankTrace`
- `Langlands.LinearAlgebra.FiniteRankTranspose`
- `Langlands.LinearAlgebra.MatrixAEvalConjugacyProof`
- `Langlands.LinearAlgebra.MatrixAEvalConjugacyStatement`
- `Langlands.LinearAlgebra.MatrixCharpolyConjugacyProof`
- `Langlands.LinearAlgebra.MatrixCharpolyConjugacyStatement`
- `Langlands.LinearAlgebra.MatrixTransposeConjugateProof`
- `Langlands.LinearAlgebra.MatrixTransposeConjugateStatement`
- `Langlands.LinearAlgebra.PolynomialModuleBoundedCyclicDecompositionProof`
- `Langlands.LinearAlgebra.PolynomialModuleBoundedCyclicDecompositionStatement`
- `Langlands.LocalFactor.Euler`
- `Langlands.LocalFactor.Euler.Definitions`
- `Langlands.LocalFactor.Harmonic.Statement`
- `Langlands.LocalFactor.RankOne`
- `Langlands.LocalField.Canonical`
- `Langlands.LocalField.CanonicalProof`
- `Langlands.LocalField.CanonicalStatement`
- `Langlands.LocalField.Definitions`
- `Langlands.LocalField.Normalization.Definitions`
- `Langlands.LocalField.Normalization.Proof`
- `Langlands.LocalField.Normalization.Statement`
- `Langlands.LocalField.SmoothCharacterNormProof`
- `Langlands.LocalField.SmoothCharacterNormStatement`
- `Langlands.LocalField.Topology`
- `Langlands.LocalField.Uniformizer`
- `Langlands.Representation.Category.Abelian`
- `Langlands.Representation.Category.Basic`
- `Langlands.Representation.Category.ClassInvariants`
- `Langlands.Representation.Category.ConstituentDichotomy`
- `Langlands.Representation.Category.ConstituentDichotomyStatement`
- `Langlands.Representation.Category.Contragredient`
- `Langlands.Representation.Category.FiniteIndexRestriction`
- `Langlands.Representation.Category.FiniteIndexSemisimplicity`
- `Langlands.Representation.Category.FiniteIndexSemisimplicityStatement`
- `Langlands.Representation.Category.RestrictionSubquotients`
- `Langlands.Representation.Category.Subquotients`
- `Langlands.Representation.Category.Twist`
- `Langlands.Representation.Category.UniverseLift`
- `Langlands.Representation.Character.Basic`
- `Langlands.Representation.Character.SeparationProof`
- `Langlands.Representation.Character.SeparationStatement`
- `Langlands.Representation.Character.TransportProof`
- `Langlands.Representation.Character.TransportStatement`
- `Langlands.Representation.Classification.CanonicalConstituents`
- `Langlands.Representation.Classification.CommonImageMultiplicityOneProof`
- `Langlands.Representation.Classification.CommonImageMultiplicityOneStatement`
- `Langlands.Representation.Classification.ConstituentCompatibility`
- `Langlands.Representation.Classification.ConstituentRelations`
- `Langlands.Representation.Classification.Cosocle`
- `Langlands.Representation.Classification.CuspidalIntegralTwistFreenessProof`
- `Langlands.Representation.Classification.CuspidalIntegralTwistFreenessStatement`
- `Langlands.Representation.Classification.CuspidalJacquetFunctorExactnessProof`
- `Langlands.Representation.Classification.CuspidalJacquetFunctorExactnessStatement`
- `Langlands.Representation.Classification.CuspidalJacquetFunctors`
- `Langlands.Representation.Classification.CuspidalJacquetMultiplicityProof`
- `Langlands.Representation.Classification.CuspidalJacquetMultiplicityStatement`
- `Langlands.Representation.Classification.CuspidalProductContragredient`
- `Langlands.Representation.Classification.CuspidalProductDerivativeQuotientSupport`
- `Langlands.Representation.Classification.CuspidalProductMirabolicSupportShiftProof`
- `Langlands.Representation.Classification.CuspidalProductMirabolicSupportShiftStatement`
- `Langlands.Representation.Classification.Essential`
- `Langlands.Representation.Classification.ExponentFamily`
- `Langlands.Representation.Classification.FiniteLengthProof`
- `Langlands.Representation.Classification.FiniteLengthStatement`
- `Langlands.Representation.Classification.HeadQuotientCriterionProof`
- `Langlands.Representation.Classification.HeadQuotientCriterionStatement`
- `Langlands.Representation.Classification.IrreducibleProductEmbedding`
- `Langlands.Representation.Classification.IrreducibleProductEmbeddingStatement`
- `Langlands.Representation.Classification.IrreducibleProductFiniteLengthProof`
- `Langlands.Representation.Classification.IrreducibleTwoFactorProductSwapProof`
- `Langlands.Representation.Classification.IrreducibleTwoFactorProductSwapStatement`
- `Langlands.Representation.Classification.LanglandsData`
- `Langlands.Representation.Classification.MirabolicDerivativeContragredient`
- `Langlands.Representation.Classification.MultiplicityOneConstituentProof`
- `Langlands.Representation.Classification.MultiplicityOneConstituentStatement`
- `Langlands.Representation.Classification.NonadjacentAssembly`
- `Langlands.Representation.Classification.NonadjacentLeibnizPieces`
- `Langlands.Representation.Classification.NonadjacentSpecialization`
- `Langlands.Representation.Classification.NonadjacentTwoBlock`
- `Langlands.Representation.Classification.NormalizedProductFiniteLengthProof`
- `Langlands.Representation.Classification.NormalizedProductFiniteLengthStatement`
- `Langlands.Representation.Classification.OppositeCuspidalJacquetFiltrationProof`
- `Langlands.Representation.Classification.OppositeCuspidalJacquetFiltrationStatement`
- `Langlands.Representation.Classification.OppositeJacquetQuotientDetectionProof`
- `Langlands.Representation.Classification.OppositeJacquetQuotientDetectionStatement`
- `Langlands.Representation.Classification.OppositeJacquetReciprocity`
- `Langlands.Representation.Classification.OppositeSupportJacquetAdapter`
- `Langlands.Representation.Classification.RelativeGenericityStatement`
- `Langlands.Representation.Classification.RelativeJacquetMultiplicityStatement`
- `Langlands.Representation.Classification.RelativeRegularComparisonStatement`
- `Langlands.Representation.Classification.SegmentConstituentStatement`
- `Langlands.Representation.Classification.SegmentCuspidalContent`
- `Langlands.Representation.Classification.SegmentDecreasingCuspidalProduct`
- `Langlands.Representation.Classification.SegmentHeadDecreasingSocle`
- `Langlands.Representation.Classification.SegmentHeadDerivativeSupportLengthTwo`
- `Langlands.Representation.Classification.SegmentHeadDerivativeSupportTruncationProof`
- `Langlands.Representation.Classification.SegmentHeadDerivativeSupportTruncationStatement`
- `Langlands.Representation.Classification.SegmentHeadProductFiniteness`
- `Langlands.Representation.Classification.SegmentHeadProductTerminalSupport`
- `Langlands.Representation.Classification.SegmentHeadSupportCons`
- `Langlands.Representation.Classification.SegmentHeadSupportGeneric`
- `Langlands.Representation.Classification.SegmentHeadSupportLeftExact`
- `Langlands.Representation.Classification.SegmentHeadSupportLeibniz`
- `Langlands.Representation.Classification.SegmentHeadSupportSplit`
- `Langlands.Representation.Classification.SegmentHeadSupportStep`
- `Langlands.Representation.Classification.SegmentHeadTopDerivative`
- `Langlands.Representation.Classification.SegmentInductionAdmissibilityProof`
- `Langlands.Representation.Classification.SegmentInductionAdmissibilityStatement`
- `Langlands.Representation.Classification.SegmentJacquetMultiplicityProof`
- `Langlands.Representation.Classification.SegmentJacquetMultiplicityStatement`
- `Langlands.Representation.Classification.SegmentJacquetReversal`
- `Langlands.Representation.Classification.SegmentSpecialConstituentExistenceProof`
- `Langlands.Representation.Classification.SegmentTensorReversalProof`
- `Langlands.Representation.Classification.SegmentTensorReversalStatement`
- `Langlands.Representation.Classification.SegmentTensorStabilizerProof`
- `Langlands.Representation.Classification.SegmentTensorStabilizerStatement`
- `Langlands.Representation.Classification.SegmentTruncationObstructionStatement`
- `Langlands.Representation.Classification.Segments`
- `Langlands.Representation.Classification.Supercuspidal`
- `Langlands.Representation.Classification.SupercuspidalContragredient`
- `Langlands.Representation.Classification.SupercuspidalContragredientAux`
- `Langlands.Representation.Classification.SupercuspidalContragredientProof`
- `Langlands.Representation.Classification.SupercuspidalContragredientStatement`
- `Langlands.Representation.Classification.SupercuspidalDerivativeVanishing`
- `Langlands.Representation.Classification.SupercuspidalDerivativesProof`
- `Langlands.Representation.Classification.SupercuspidalDerivativesStatement`
- `Langlands.Representation.Classification.SupercuspidalSupport`
- `Langlands.Representation.Classification.SupercuspidalSupportStatement`
- `Langlands.Representation.Classification.SupercuspidalSupportUniquenessProof`
- `Langlands.Representation.Classification.SupercuspidalTopDerivative`
- `Langlands.Representation.Classification.SupercuspidalTwist`
- `Langlands.Representation.Classification.Tempered`
- `Langlands.Representation.Classification.TemperedInductionStatement`
- `Langlands.Representation.Classification.TemperedSupportStatement`
- `Langlands.Representation.Classification.TwistedProductCharacterTwistProof`
- `Langlands.Representation.Classification.TwoBlockExponentNonUnitarizabilityProof`
- `Langlands.Representation.Classification.TwoBlockExponentNonUnitarizabilityStatement`
- `Langlands.Representation.Classification.TwoSupercuspidalAdjacentReducibilityProof`
- `Langlands.Representation.Classification.TwoSupercuspidalAdjacentReducibilityStatement`
- `Langlands.Representation.Classification.TwoSupercuspidalBinaryProductBridge`
- `Langlands.Representation.Classification.TwoSupercuspidalDerivativeBridge`
- `Langlands.Representation.Classification.TwoSupercuspidalNonadjacentIrreducibilityProof`
- `Langlands.Representation.Classification.TwoSupercuspidalProductDualTwist`
- `Langlands.Representation.Classification.TwoSupercuspidalProductStructureStatement`
- `Langlands.Representation.Classification.UnitaryGenericCompatibilityStatement`
- `Langlands.Representation.Classification.UpperCuspidalJacquetMultiplicityProof`
- `Langlands.Representation.Classification.UpperCuspidalJacquetMultiplicityStatement`
- `Langlands.Representation.Classification.UpperJacquetSubrepresentationDetectionProof`
- `Langlands.Representation.Classification.UpperJacquetSubrepresentationDetectionStatement`
- `Langlands.Representation.Compact.Definitions`
- `Langlands.Representation.Compact.FiniteMean`
- `Langlands.Representation.Compact.OrbitMeanTranslation`
- `Langlands.Representation.Compact.ProjectionProof`
- `Langlands.Representation.Compact.ProjectionStatement`
- `Langlands.Representation.Compact.SurjectivityProof`
- `Langlands.Representation.Compact.SurjectivityStatement`
- `Langlands.Representation.CompactCoefficient.AdmissibleComplement`
- `Langlands.Representation.CompactCoefficient.AdmissibleLifting`
- `Langlands.Representation.CompactCoefficient.AdmissibleRetraction`
- `Langlands.Representation.CompactCoefficient.AmbientProjector`
- `Langlands.Representation.CompactCoefficient.Classes`
- `Langlands.Representation.CompactCoefficient.ConditionalProjection`
- `Langlands.Representation.CompactCoefficient.FixedLevelFiniteness`
- `Langlands.Representation.CompactCoefficient.FixedVectorsFiniteDimensional`
- `Langlands.Representation.CompactCoefficient.GroupTransport`
- `Langlands.Representation.CompactCoefficient.Isotypic`
- `Langlands.Representation.CompactCoefficient.IsotypicTransport`
- `Langlands.Representation.CompactCoefficient.NormalSubgroupDecomposition`
- `Langlands.Representation.CompactCoefficient.OrthogonalProjectorFamily`
- `Langlands.Representation.CompactCoefficient.SelectedAssembly`
- `Langlands.Representation.CompactCoefficient.SelectedBlock`
- `Langlands.Representation.CompactCoefficient.SelectedConjugation`
- `Langlands.Representation.CompactCoefficient.SelectedCoverage`
- `Langlands.Representation.CompactCoefficient.SelectedProjector`
- `Langlands.Representation.CompactCoefficient.SemisimplicityProof`
- `Langlands.Representation.CompactCoefficient.SemisimplicityStatement`
- `Langlands.Representation.CompactCoefficient.TotalCompactness`
- `Langlands.Representation.CompactCoefficient.TotalProjector`
- `Langlands.Representation.Conductor.Congruence`
- `Langlands.Representation.Conductor.Definitions`
- `Langlands.Representation.Conductor.PrincipalCongruence`
- `Langlands.Representation.Conductor.PrincipalCongruenceBasisProof`
- `Langlands.Representation.Conductor.PrincipalCongruenceBasisStatement`
- `Langlands.Representation.CuspidalSupport.AllRankBinaryCuspidalConcatenation`
- `Langlands.Representation.CuspidalSupport.AssociatedAssembly`
- `Langlands.Representation.CuspidalSupport.AssociatedConditional`
- `Langlands.Representation.CuspidalSupport.AssociatedGeometricPieceVanishingProof`
- `Langlands.Representation.CuspidalSupport.AssociatedGeometricPiecesEquivalenceProof`
- `Langlands.Representation.CuspidalSupport.AssociatedGeometricPiecesProof`
- `Langlands.Representation.CuspidalSupport.AssociatedGeometricPiecesStatement`
- `Langlands.Representation.CuspidalSupport.AssociatedProof`
- `Langlands.Representation.CuspidalSupport.AssociatedRankZero`
- `Langlands.Representation.CuspidalSupport.AssociationForwardHomProof`
- `Langlands.Representation.CuspidalSupport.AssociationForwardHomSupport`
- `Langlands.Representation.CuspidalSupport.AssociationForwardStatement`
- `Langlands.Representation.CuspidalSupport.AssociationLawsProof`
- `Langlands.Representation.CuspidalSupport.AssociationLawsStatement`
- `Langlands.Representation.CuspidalSupport.AssociationReduction`
- `Langlands.Representation.CuspidalSupport.AssociationReverseProof`
- `Langlands.Representation.CuspidalSupport.AssociationReverseStatement`
- `Langlands.Representation.CuspidalSupport.BinaryCuspidalConcatenation`
- `Langlands.Representation.CuspidalSupport.BinaryProductSupport`
- `Langlands.Representation.CuspidalSupport.BlockMap`
- `Langlands.Representation.CuspidalSupport.BlockPermutation`
- `Langlands.Representation.CuspidalSupport.BlockWeylTransport`
- `Langlands.Representation.CuspidalSupport.CentralShift`
- `Langlands.Representation.CuspidalSupport.CompactCoefficientFinitenessProof`
- `Langlands.Representation.CuspidalSupport.CompactCoefficientFinitenessReduction`
- `Langlands.Representation.CuspidalSupport.CompactCoefficientFinitenessStatement`
- `Langlands.Representation.CuspidalSupport.ConstituentComplement`
- `Langlands.Representation.CuspidalSupport.ConstituentComplementStatement`
- `Langlands.Representation.CuspidalSupport.ConstituentFiniteTypes`
- `Langlands.Representation.CuspidalSupport.ConstituentInduction`
- `Langlands.Representation.CuspidalSupport.ConstituentInductionStatement`
- `Langlands.Representation.CuspidalSupport.ConstituentProof`
- `Langlands.Representation.CuspidalSupport.ConstituentRankZero`
- `Langlands.Representation.CuspidalSupport.ConstituentSemisimple`
- `Langlands.Representation.CuspidalSupport.ConstituentSemisimpleStatement`
- `Langlands.Representation.CuspidalSupport.CuspidalBlockIsolationProof`
- `Langlands.Representation.CuspidalSupport.CuspidalBlockIsolationStatement`
- `Langlands.Representation.CuspidalSupport.CuspidalEmbeddingProof`
- `Langlands.Representation.CuspidalSupport.CuspidalTensorAssociationProof`
- `Langlands.Representation.CuspidalSupport.CuspidalTensorProof`
- `Langlands.Representation.CuspidalSupport.CuspidalTensorStatement`
- `Langlands.Representation.CuspidalSupport.CuspidalityComparisonProof`
- `Langlands.Representation.CuspidalSupport.CuspidalityComparisonStatement`
- `Langlands.Representation.CuspidalSupport.DeterminantUnit`
- `Langlands.Representation.CuspidalSupport.DeterminantUnitCartanSupport`
- `Langlands.Representation.CuspidalSupport.DeterminantUnitCentralCompactnessProof`
- `Langlands.Representation.CuspidalSupport.DeterminantUnitCentralCompactnessStatement`
- `Langlands.Representation.CuspidalSupport.DeterminantUnitCornerStructureProof`
- `Langlands.Representation.CuspidalSupport.DeterminantUnitCornerStructureStatement`
- `Langlands.Representation.CuspidalSupport.DeterminantUnitFiniteRestriction`
- `Langlands.Representation.CuspidalSupport.DeterminantUnitStructureProof`
- `Langlands.Representation.CuspidalSupport.DeterminantUnitStructureStatement`
- `Langlands.Representation.CuspidalSupport.DistinctTensorStabilizerProof`
- `Langlands.Representation.CuspidalSupport.DistinctTensorStabilizerStatement`
- `Langlands.Representation.CuspidalSupport.DualAveraging`
- `Langlands.Representation.CuspidalSupport.FiltrationQuasicuspidality`
- `Langlands.Representation.CuspidalSupport.FiniteBlockShapes`
- `Langlands.Representation.CuspidalSupport.GroupTransport`
- `Langlands.Representation.CuspidalSupport.HarishChandraAssembly`
- `Langlands.Representation.CuspidalSupport.HarishChandraBoundaryProof`
- `Langlands.Representation.CuspidalSupport.HarishChandraBoundaryStatement`
- `Langlands.Representation.CuspidalSupport.HarishChandraConverseProof`
- `Langlands.Representation.CuspidalSupport.HarishChandraConverseStatement`
- `Langlands.Representation.CuspidalSupport.HarishChandraForwardProof`
- `Langlands.Representation.CuspidalSupport.HarishChandraStatement`
- `Langlands.Representation.CuspidalSupport.InducedJacquetCount`
- `Langlands.Representation.CuspidalSupport.InducedJacquetEvaluation`
- `Langlands.Representation.CuspidalSupport.IrreducibleLeviAdmissibilityProof`
- `Langlands.Representation.CuspidalSupport.IrreducibleLeviAdmissibilityStatement`
- `Langlands.Representation.CuspidalSupport.JacquetDetectingFamilyLengthProof`
- `Langlands.Representation.CuspidalSupport.JacquetDetectingFamilyLengthStatement`
- `Langlands.Representation.CuspidalSupport.JacquetInductionStatement`
- `Langlands.Representation.CuspidalSupport.JacquetLengthDetector`
- `Langlands.Representation.CuspidalSupport.JacquetSubquotientProof`
- `Langlands.Representation.CuspidalSupport.JacquetSubquotientStatement`
- `Langlands.Representation.CuspidalSupport.JacquetVanishingHelpers`
- `Langlands.Representation.CuspidalSupport.JacquetVanishingSmoothPieces`
- `Langlands.Representation.CuspidalSupport.JacquetVanishingSubgroups`
- `Langlands.Representation.CuspidalSupport.LeviAdmissibleFactorizationProof`
- `Langlands.Representation.CuspidalSupport.LeviAdmissibleFactorizationStatement`
- `Langlands.Representation.CuspidalSupport.LeviAssociation`
- `Langlands.Representation.CuspidalSupport.LeviCompactPart`
- `Langlands.Representation.CuspidalSupport.LeviDecompositionAssembly`
- `Langlands.Representation.CuspidalSupport.LeviDefinitions`
- `Langlands.Representation.CuspidalSupport.LeviGapVanishing`
- `Langlands.Representation.CuspidalSupport.LeviQuasicuspidalDecompositionProof`
- `Langlands.Representation.CuspidalSupport.LeviSplitContraction`
- `Langlands.Representation.CuspidalSupport.LeviTensorFactorizationProof`
- `Langlands.Representation.CuspidalSupport.LeviTensorFactorizationStatement`
- `Langlands.Representation.CuspidalSupport.LeviTensorReflectionProof`
- `Langlands.Representation.CuspidalSupport.LeviTensorReflectionStatement`
- `Langlands.Representation.CuspidalSupport.MinimalConjugatingCosetsProof`
- `Langlands.Representation.CuspidalSupport.MinimalJacquetProof`
- `Langlands.Representation.CuspidalSupport.MinimalJacquetStatement`
- `Langlands.Representation.CuspidalSupport.MinimalRefinedJacquetProof`
- `Langlands.Representation.CuspidalSupport.MinimalRefinedJacquetStatement`
- `Langlands.Representation.CuspidalSupport.MinimalWeylTransportProof`
- `Langlands.Representation.CuspidalSupport.NaturalProjectorDecomposition`
- `Langlands.Representation.CuspidalSupport.NonassociatedJacquetSubquotientsProof`
- `Langlands.Representation.CuspidalSupport.NormalizedCuspidalInductionLengthProof`
- `Langlands.Representation.CuspidalSupport.NormalizedCuspidalInductionStatement`
- `Langlands.Representation.CuspidalSupport.PointwiseProjectorSum`
- `Langlands.Representation.CuspidalSupport.ProperInductionMaps`
- `Langlands.Representation.CuspidalSupport.ProperInductionProof`
- `Langlands.Representation.CuspidalSupport.ProperInductionStatement`
- `Langlands.Representation.CuspidalSupport.QuasicuspidalEmbeddingProof`
- `Langlands.Representation.CuspidalSupport.QuasicuspidalFiniteLengthProof`
- `Langlands.Representation.CuspidalSupport.QuasicuspidalFiniteLengthStatement`
- `Langlands.Representation.CuspidalSupport.QuasicuspidalLeviAdmissibilityProof`
- `Langlands.Representation.CuspidalSupport.QuasicuspidalPrerequisitesStatement`
- `Langlands.Representation.CuspidalSupport.QuasicuspidalStructureStatement`
- `Langlands.Representation.CuspidalSupport.RefinedJacquetLengthProof`
- `Langlands.Representation.CuspidalSupport.RefinedJacquetLengthStatement`
- `Langlands.Representation.CuspidalSupport.RefinedQuasicuspidalEmbeddingProof`
- `Langlands.Representation.CuspidalSupport.RefinedQuasicuspidalEmbeddingStatement`
- `Langlands.Representation.CuspidalSupport.StandardJacquetComparisonProof`
- `Langlands.Representation.CuspidalSupport.TotalConjugatingCountProof`
- `Langlands.Representation.CuspidalSupport.TotalConjugatingCountStatement`
- `Langlands.Representation.CuspidalSupport.WholeLeviTransport`
- `Langlands.Representation.CuspidalSupport.ZeroRankEmbeddingProof`
- `Langlands.Representation.Derivative.BinaryDerivativeSupportAggregation`
- `Langlands.Representation.Derivative.DerivativeEquivTransport`
- `Langlands.Representation.Derivative.GeneralLinearDerivativeExactnessProof`
- `Langlands.Representation.Derivative.GeneralLinearDerivativeExactnessStatement`
- `Langlands.Representation.Derivative.GeneralLinearDerivativeFiniteLengthProof`
- `Langlands.Representation.Derivative.GeneralLinearDerivativeFiniteLengthStatement`
- `Langlands.Representation.Derivative.GeneralLinearDerivativeLeibnizBoundary`
- `Langlands.Representation.Derivative.GeneralLinearDerivativeLeibnizFiltrationProof`
- `Langlands.Representation.Derivative.GeneralLinearDerivativeLeibnizFiltrationStatement`
- `Langlands.Representation.Derivative.Homogeneity`
- `Langlands.Representation.Derivative.Iteration`
- `Langlands.Representation.Derivative.LeftMixedProductDerivativeProof`
- `Langlands.Representation.Derivative.LeftMixedProductHigher`
- `Langlands.Representation.Derivative.LeftMixedProductHomogeneityProof`
- `Langlands.Representation.Derivative.LeftMixedProductHomogeneityStatement`
- `Langlands.Representation.Derivative.LeftMixedProductPhiHatIterate`
- `Langlands.Representation.Derivative.LeftMixedProductVanishing`
- `Langlands.Representation.Derivative.LeftMixedProductZeroRank`
- `Langlands.Representation.Derivative.LeibnizConstituentExtraction`
- `Langlands.Representation.Derivative.LeibnizIndices`
- `Langlands.Representation.Derivative.LeibnizPieceCompat`
- `Langlands.Representation.Derivative.LeibnizPositiveGluing`
- `Langlands.Representation.Derivative.LeibnizQuotientPiece`
- `Langlands.Representation.Derivative.LeibnizRankZeroBoundary`
- `Langlands.Representation.Derivative.LeibnizRankZeroGluing`
- `Langlands.Representation.Derivative.LeibnizRestrictionCompat`
- `Langlands.Representation.Derivative.LeibnizRestrictionExact`
- `Langlands.Representation.Derivative.LeibnizZeroFirstPiece`
- `Langlands.Representation.Derivative.LevelCalculus`
- `Langlands.Representation.Derivative.MinusVanishing`
- `Langlands.Representation.Derivative.MirabolicCharacter`
- `Langlands.Representation.Derivative.MirabolicDerivativeDetectionProof`
- `Langlands.Representation.Derivative.MirabolicDerivativeDetectionStatement`
- `Langlands.Representation.Derivative.MirabolicDerivativeUnitInjective`
- `Langlands.Representation.Derivative.MirabolicDerivativeVanishing`
- `Langlands.Representation.Derivative.MirabolicDeterminant`
- `Langlands.Representation.Derivative.MirabolicHighestDerivativeDescent`
- `Langlands.Representation.Derivative.MirabolicHighestDerivativePairingProof`
- `Langlands.Representation.Derivative.MirabolicHighestDerivativePairingStatement`
- `Langlands.Representation.Derivative.MirabolicLatticeBox`
- `Langlands.Representation.Derivative.MirabolicMinus`
- `Langlands.Representation.Derivative.MirabolicMinusExactnessProof`
- `Langlands.Representation.Derivative.MirabolicMinusExactnessStatement`
- `Langlands.Representation.Derivative.MirabolicMinusNormalization`
- `Langlands.Representation.Derivative.MirabolicMinusPairingTransferProof`
- `Langlands.Representation.Derivative.MirabolicMinusPairingTransferStatement`
- `Langlands.Representation.Derivative.MirabolicMixedOrbitCharacters`
- `Langlands.Representation.Derivative.MirabolicPhiMinusMackey`
- `Langlands.Representation.Derivative.MirabolicPhiMinusNondegeneratePairing`
- `Langlands.Representation.Derivative.MirabolicPlus`
- `Langlands.Representation.Derivative.MirabolicPlusNormalization`
- `Langlands.Representation.Derivative.MirabolicProductMinusBoundary`
- `Langlands.Representation.Derivative.MirabolicProductMinusCompatibility`
- `Langlands.Representation.Derivative.MirabolicProductMinusCompatibilityStatement`
- `Langlands.Representation.Derivative.MirabolicProductMinusLeftPhi`
- `Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiCoefficient`
- `Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiCompactComparison`
- `Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiHaar`
- `Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiHostTransport`
- `Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiIdentityComparison`
- `Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiInductionNormalization`
- `Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiLocalization`
- `Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiMackeyLocalization`
- `Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiNormalization`
- `Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiNormalizedSection`
- `Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiSection`
- `Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiSourceAction`
- `Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiSourceComparison`
- `Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiStagesComparison`
- `Langlands.Representation.Derivative.MirabolicProductMinusLeftPsi`
- `Langlands.Representation.Derivative.MirabolicProductMinusLeftPsiInduction`
- `Langlands.Representation.Derivative.MirabolicProductMinusPhiKernelComparison`
- `Langlands.Representation.Derivative.MirabolicProductMinusRightBoundary`
- `Langlands.Representation.Derivative.MirabolicProductMinusRightPhi`
- `Langlands.Representation.Derivative.MirabolicProductMinusRightPhiAssembly`
- `Langlands.Representation.Derivative.MirabolicProductMinusRightPhiCycle`
- `Langlands.Representation.Derivative.MirabolicProductMinusRightPhiCycleCoefficient`
- `Langlands.Representation.Derivative.MirabolicProductMinusRightPhiCycleGroups`
- `Langlands.Representation.Derivative.MirabolicProductMinusRightPhiIdentity`
- `Langlands.Representation.Derivative.MirabolicProductMinusRightPhiIdentityCoefficient`
- `Langlands.Representation.Derivative.MirabolicProductMinusRightPhiIdentityGroups`
- `Langlands.Representation.Derivative.MirabolicProductMinusRightPsi`
- `Langlands.Representation.Derivative.MirabolicProductMinusRightPsiCoefficient`
- `Langlands.Representation.Derivative.MirabolicProductMinusRightPsiGroups`
- `Langlands.Representation.Derivative.MirabolicProductMinusRightPsiZero`
- `Langlands.Representation.Derivative.MirabolicProductRestriction`
- `Langlands.Representation.Derivative.MirabolicProductRestrictionCasts`
- `Langlands.Representation.Derivative.MirabolicProductRestrictionFactors`
- `Langlands.Representation.Derivative.MirabolicProductRestrictionMackey`
- `Langlands.Representation.Derivative.MirabolicProductRestrictionOrbits`
- `Langlands.Representation.Derivative.MirabolicProductRestrictionStabilizers`
- `Langlands.Representation.Derivative.MirabolicProductRestrictionStatement`
- `Langlands.Representation.Derivative.MirabolicProductRestrictionTransport`
- `Langlands.Representation.Derivative.MirabolicSmoothPhiPlus`
- `Langlands.Representation.Derivative.MirabolicSmoothPhiPlusAdjunction`
- `Langlands.Representation.Derivative.MirabolicSmoothPhiPlusIterate`
- `Langlands.Representation.Derivative.MirabolicSmoothPhiPlusProduct`
- `Langlands.Representation.Derivative.MixedProductDerivativeStatement`
- `Langlands.Representation.Derivative.MixedProductRankCast`
- `Langlands.Representation.Derivative.OrderRecursion`
- `Langlands.Representation.Derivative.OrderedCuspidalProductHeadShift`
- `Langlands.Representation.Derivative.OrderedCuspidalProductNondegeneracyProof`
- `Langlands.Representation.Derivative.OrderedCuspidalProductNondegeneracyStatement`
- `Langlands.Representation.Derivative.OrderedCuspidalProductTwistOne`
- `Langlands.Representation.Derivative.Partial`
- `Langlands.Representation.Derivative.PartialDerivativeJacquetComparisonProof`
- `Langlands.Representation.Derivative.PartialDerivativeJacquetComparisonStatement`
- `Langlands.Representation.Derivative.PartialDerivativeJacquetLHS`
- `Langlands.Representation.Derivative.PartialDerivativeJacquetNormalization`
- `Langlands.Representation.Derivative.PartialDerivativeJacquetRHS`
- `Langlands.Representation.Derivative.PartialDerivativeJacquetRHSComparison`
- `Langlands.Representation.Derivative.PartialLocalizationCharacter`
- `Langlands.Representation.Derivative.PartialLocalizationData`
- `Langlands.Representation.Derivative.ProductDerivativeSupportAggregation`
- `Langlands.Representation.Derivative.ProductDerivativesFiniteLength`
- `Langlands.Representation.Derivative.ProductVanishing`
- `Langlands.Representation.Derivative.RankCastCompat`
- `Langlands.Representation.Derivative.RestrictedProductLevel`
- `Langlands.Representation.Derivative.RestrictionBridge`
- `Langlands.Representation.Derivative.RightMixedLevel`
- `Langlands.Representation.Derivative.RightMixedProductDerivativeFiltrationProof`
- `Langlands.Representation.Derivative.RightMixedProductDerivativeFiltrationStatement`
- `Langlands.Representation.Derivative.RightMixedProductDerivativePositive`
- `Langlands.Representation.Derivative.RightMixedProductPhiMinusDetectionProof`
- `Langlands.Representation.Derivative.RightMixedProductZeroRank`
- `Langlands.Representation.Derivative.ShortExactFunctorLaws`
- `Langlands.Representation.Derivative.TopLine`
- `Langlands.Representation.Derivative.TopLocalizationData`
- `Langlands.Representation.Derivative.ZeroRankTensor`
- `Langlands.Representation.Dual.Definitions`
- `Langlands.Representation.Exponents.Central`
- `Langlands.Representation.Exponents.ComplexTwistFamilies`
- `Langlands.Representation.Exponents.DualJacquet`
- `Langlands.Representation.Exponents.DualJacquetStatement`
- `Langlands.Representation.Exponents.Jacquet`
- `Langlands.Representation.Exponents.NilpotenceIndex`
- `Langlands.Representation.Exponents.ParabolicPair`
- `Langlands.Representation.Exponents.RealTwistFamilies`
- `Langlands.Representation.Exponents.SupportedRegularMultiplicityBranchObstructionStatement`
- `Langlands.Representation.Exponents.UnitaryDualJacquetSupportAdapters`
- `Langlands.Representation.Exponents.WeylBranchPiecesStatement`
- `Langlands.Representation.Exponents.WeylBranchPiecesSubquotient`
- `Langlands.Representation.Filtration.ActualGradedExtraction`
- `Langlands.Representation.Filtration.CoarseJacquetExtraction`
- `Langlands.Representation.Filtration.CoarseJacquetFactorization`
- `Langlands.Representation.Filtration.CoinvariantVanishingStatement`
- `Langlands.Representation.Filtration.CommonSubquotientStatement`
- `Langlands.Representation.Filtration.Definitions`
- `Langlands.Representation.Filtration.ExactConstituentExtraction`
- `Langlands.Representation.Filtration.ExactSmoothSubquotients`
- `Langlands.Representation.Filtration.ExactSmoothTransport`
- `Langlands.Representation.Filtration.FactorMatchingPullback`
- `Langlands.Representation.Filtration.FiniteFamilyMultiplicityProof`
- `Langlands.Representation.Filtration.FiniteFamilyMultiplicityStatement`
- `Langlands.Representation.Filtration.FunctorLengthTwoDetection`
- `Langlands.Representation.Filtration.GluedFamily`
- `Langlands.Representation.Filtration.GradedRefinementProof`
- `Langlands.Representation.Filtration.GradedRefinementStatement`
- `Langlands.Representation.Filtration.IntervalLiftProof`
- `Langlands.Representation.Filtration.IntervalLiftStatement`
- `Langlands.Representation.Filtration.InvariantBilinear`
- `Langlands.Representation.Filtration.InvariantBilinearBounds`
- `Langlands.Representation.Filtration.InvariantBilinearSubquotientBounds`
- `Langlands.Representation.Filtration.IrreducibleEmbedding`
- `Langlands.Representation.Filtration.IrreducibleMultiplicityProof`
- `Langlands.Representation.Filtration.IrreducibleMultiplicityStatement`
- `Langlands.Representation.Filtration.IsoTransport`
- `Langlands.Representation.Filtration.JordanHolderComparisonProof`
- `Langlands.Representation.Filtration.JordanHolderProof`
- `Langlands.Representation.Filtration.JordanHolderStatement`
- `Langlands.Representation.Filtration.JordanHolderTransportProof`
- `Langlands.Representation.Filtration.LengthCriterionProof`
- `Langlands.Representation.Filtration.LengthCriterionStatement`
- `Langlands.Representation.Filtration.LengthTwoMatching`
- `Langlands.Representation.Filtration.LengthTwoMatchingStatement`
- `Langlands.Representation.Filtration.MultiplicityAdditivityProof`
- `Langlands.Representation.Filtration.MultiplicityAdditivityStatement`
- `Langlands.Representation.Filtration.MultiplicityIndependenceProof`
- `Langlands.Representation.Filtration.MultiplicityStatement`
- `Langlands.Representation.Filtration.MultiplicityTransportProof`
- `Langlands.Representation.Filtration.MultiplicityTransportStatement`
- `Langlands.Representation.Filtration.NonzeroHomCommonSubquotientProof`
- `Langlands.Representation.Filtration.NonzeroHomCommonSubquotientStatement`
- `Langlands.Representation.Filtration.ObjectDefinitions`
- `Langlands.Representation.Filtration.ObjectTransport`
- `Langlands.Representation.Filtration.OneStep`
- `Langlands.Representation.Filtration.Precomposition`
- `Langlands.Representation.Filtration.QuasicuspidalVanishingProof`
- `Langlands.Representation.Filtration.QuotientFirstIso`
- `Langlands.Representation.Filtration.QuotientTail`
- `Langlands.Representation.Filtration.RepresentationLength`
- `Langlands.Representation.Filtration.SimpleMapMultiplicityDetectionProof`
- `Langlands.Representation.Filtration.SimpleMapMultiplicityDetectionStatement`
- `Langlands.Representation.Filtration.SimpleSubquotientFactorProof`
- `Langlands.Representation.Filtration.SimpleSubquotientFactorStatement`
- `Langlands.Representation.Filtration.SmoothDualEvaluation`
- `Langlands.Representation.Filtration.SmoothGradedObject`
- `Langlands.Representation.Filtration.Splicing`
- `Langlands.Representation.Filtration.Splicing.Basic`
- `Langlands.Representation.Filtration.SubquotientAlgebraProof`
- `Langlands.Representation.Filtration.SubquotientAlgebraStatement`
- `Langlands.Representation.Filtration.SubsingletonProof`
- `Langlands.Representation.Filtration.Transport`
- `Langlands.Representation.Filtration.VanishingStatement`
- `Langlands.Representation.Filtration.ZeroFactorDeletionProof`
- `Langlands.Representation.Filtration.ZeroFactorDeletionStatement`
- `Langlands.Representation.Geometric.BlockIntersectionSplitting`
- `Langlands.Representation.Geometric.BlockSixDecomposableProof`
- `Langlands.Representation.Geometric.BlockSixDecomposableStatement`
- `Langlands.Representation.Geometric.BruhatDescent`
- `Langlands.Representation.Geometric.BruhatMatrixExistenceProof`
- `Langlands.Representation.Geometric.BruhatMatrixStatement`
- `Langlands.Representation.Geometric.BruhatWeylReflectionProof`
- `Langlands.Representation.Geometric.ClosedSubgroupAssembly`
- `Langlands.Representation.Geometric.ClosedSubgroupDefinitions`
- `Langlands.Representation.Geometric.ClosedSubgroupMackeyProof`
- `Langlands.Representation.Geometric.ClosedSubgroupStatement`
- `Langlands.Representation.Geometric.CoarseLeviReversal`
- `Langlands.Representation.Geometric.CompactOrbitRestriction`
- `Langlands.Representation.Geometric.CompactSmoothComparison`
- `Langlands.Representation.Geometric.ConditionalAssembly`
- `Langlands.Representation.Geometric.CorrectionSubgroupCoordinates`
- `Langlands.Representation.Geometric.CorrectionSubgroupDiagonalHaarProof`
- `Langlands.Representation.Geometric.CorrectionSubgroupDiagonalHaarStatement`
- `Langlands.Representation.Geometric.CosetAction`
- `Langlands.Representation.Geometric.CosetOrbitHomeomorph`
- `Langlands.Representation.Geometric.CosetOrbitOrdering`
- `Langlands.Representation.Geometric.FlattenedLevi`
- `Langlands.Representation.Geometric.GeneralCorrectionCharacters`
- `Langlands.Representation.Geometric.GeneralIntersectionNormalizers`
- `Langlands.Representation.Geometric.GeneralIntersections`
- `Langlands.Representation.Geometric.GeometricLemmaProof`
- `Langlands.Representation.Geometric.GeometricLemmaStatement`
- `Langlands.Representation.Geometric.IntersectionLeviDiagonalCharacterProof`
- `Langlands.Representation.Geometric.IntersectionLeviDiagonalCharacterStatement`
- `Langlands.Representation.Geometric.IntersectionLeviModulusBalance`
- `Langlands.Representation.Geometric.IntersectionTransport`
- `Langlands.Representation.Geometric.MonotoneBlocksProof`
- `Langlands.Representation.Geometric.MonotoneBlocksStatement`
- `Langlands.Representation.Geometric.OrbitRepresentatives`
- `Langlands.Representation.Geometric.OrbitRestriction`
- `Langlands.Representation.Geometric.OrbitSectionExtensionProof`
- `Langlands.Representation.Geometric.OrbitSectionExtensionStatement`
- `Langlands.Representation.Geometric.PadicCorrectionCancellationProof`
- `Langlands.Representation.Geometric.PadicCorrectionCancellationStatement`
- `Langlands.Representation.Geometric.PadicParabolicBruhatProof`
- `Langlands.Representation.Geometric.ParabolicOrbitCoefficientComparison`
- `Langlands.Representation.Geometric.ParabolicOrbitCompactComparison`
- `Langlands.Representation.Geometric.ParabolicOrbitComparisonData`
- `Langlands.Representation.Geometric.ParabolicOrbitHaarComparison`
- `Langlands.Representation.Geometric.ParabolicOrbitHaarRatio`
- `Langlands.Representation.Geometric.ParabolicOrbitHaarTransport`
- `Langlands.Representation.Geometric.ParabolicOrbitInductionTransport`
- `Langlands.Representation.Geometric.ParabolicOrbitJacquet`
- `Langlands.Representation.Geometric.ParabolicOrbitJacquetProof`
- `Langlands.Representation.Geometric.ParabolicOrbitJacquetStatement`
- `Langlands.Representation.Geometric.ParabolicOrbitMeasureData`
- `Langlands.Representation.Geometric.ParabolicOrbitNestedAction`
- `Langlands.Representation.Geometric.ParabolicOrbitNormalization`
- `Langlands.Representation.Geometric.ParabolicOrbitNormalizedCoefficient`
- `Langlands.Representation.Geometric.ParabolicOrbitSectionComparison`
- `Langlands.Representation.Geometric.ParabolicOrbitStagesCoefficient`
- `Langlands.Representation.Geometric.ParabolicSupportFiltration`
- `Langlands.Representation.Geometric.ParabolicSupportGradedProof`
- `Langlands.Representation.Geometric.ParabolicSupportGradedStatement`
- `Langlands.Representation.Geometric.ParabolicSupportJacquetProof`
- `Langlands.Representation.Geometric.ParabolicSupportJacquetStatement`
- `Langlands.Representation.Geometric.ParabolicSupportTransport`
- `Langlands.Representation.Geometric.RefinedPositiveCharacter`
- `Langlands.Representation.Geometric.RefinementDefinitions`
- `Langlands.Representation.Geometric.RefinementFunctors`
- `Langlands.Representation.Geometric.RefinementUniqueness`
- `Langlands.Representation.Geometric.SmoothSupportFiltration`
- `Langlands.Representation.Geometric.StandardIntersectionsProof`
- `Langlands.Representation.Geometric.WeylDefinitions`
- `Langlands.Representation.Geometric.WeylMinimalRepresentativeProof`
- `Langlands.Representation.Geometric.WeylStatement`
- `Langlands.Representation.Geometric.WeylUniquenessProof`
- `Langlands.Representation.Geometric.WeylUniquenessStatement`
- `Langlands.Representation.Hecke.ActionIntegrand`
- `Langlands.Representation.Hecke.ActionLocalUnits`
- `Langlands.Representation.Hecke.ActionProjection`
- `Langlands.Representation.Hecke.AntiPullback`
- `Langlands.Representation.Hecke.CommonInvarianceProof`
- `Langlands.Representation.Hecke.CommonInvarianceStatement`
- `Langlands.Representation.Hecke.Convolution`
- `Langlands.Representation.Hecke.Corner`
- `Langlands.Representation.Hecke.CornerAction`
- `Langlands.Representation.Hecke.CornerDetermination`
- `Langlands.Representation.Hecke.DoubleCoset`
- `Langlands.Representation.Hecke.DoubleCosetSandwich`
- `Langlands.Representation.Hecke.FiniteRankAction`
- `Langlands.Representation.Hecke.IntegratedAction`
- `Langlands.Representation.Hecke.IntegratedConvolution`
- `Langlands.Representation.Hecke.NormalizedIndicator`
- `Langlands.Representation.Hecke.SmoothTranspose`
- `Langlands.Representation.Hecke.TestFunction`
- `Langlands.Representation.Induction.BinaryPositiveCompact`
- `Langlands.Representation.Induction.BinaryProduct`
- `Langlands.Representation.Induction.BinaryProductConstituentExtraction`
- `Langlands.Representation.Induction.BinaryProductSubquotients`
- `Langlands.Representation.Induction.BlockCharacterAbsorption`
- `Langlands.Representation.Induction.BlockEquivalence`
- `Langlands.Representation.Induction.BlockFactors`
- `Langlands.Representation.Induction.CharacterTwistProof`
- `Langlands.Representation.Induction.CompactAutomorphism`
- `Langlands.Representation.Induction.CompactAutomorphismIntegralProof`
- `Langlands.Representation.Induction.CompactAutomorphismIntegralStatement`
- `Langlands.Representation.Induction.CompactBilinearPairing`
- `Langlands.Representation.Induction.CompactCoinvariantBijectivityProof`
- `Langlands.Representation.Induction.CompactCoinvariantBijectivityStatement`
- `Langlands.Representation.Induction.CompactCoinvariantIntegral`
- `Langlands.Representation.Induction.CompactCoinvariantLocalInverseProof`
- `Langlands.Representation.Induction.CompactCoinvariantLocalInverseStatement`
- `Langlands.Representation.Induction.CompactIntegralForm`
- `Langlands.Representation.Induction.CompactLocalSection`
- `Langlands.Representation.Induction.CompactLocalSectionSpanningProof`
- `Langlands.Representation.Induction.CompactLocalSectionSpanningStatement`
- `Langlands.Representation.Induction.CompactLocallyConstant`
- `Langlands.Representation.Induction.CompactPairingDuality`
- `Langlands.Representation.Induction.CompactQuotientCutoff`
- `Langlands.Representation.Induction.CompactQuotientProof`
- `Langlands.Representation.Induction.CompactScalarProof`
- `Langlands.Representation.Induction.CompactScalarStatement`
- `Langlands.Representation.Induction.CompactSurjectivityProof`
- `Langlands.Representation.Induction.CompactSurjectivityStatement`
- `Langlands.Representation.Induction.CompactTransitivityProof`
- `Langlands.Representation.Induction.CompactTransitivityStatement`
- `Langlands.Representation.Induction.ConjugateParabolic`
- `Langlands.Representation.Induction.CovariantRescaling`
- `Langlands.Representation.Induction.Definitions`
- `Langlands.Representation.Induction.EmptyProductUnit`
- `Langlands.Representation.Induction.Equivalences`
- `Langlands.Representation.Induction.FiniteProductTensor`
- `Langlands.Representation.Induction.FiniteProductTensorBijectiveProof`
- `Langlands.Representation.Induction.FiniteProductTensorBijectiveStatement`
- `Langlands.Representation.Induction.HeadTailBinaryProduct`
- `Langlands.Representation.Induction.HeterogeneousConstruction`
- `Langlands.Representation.Induction.HeterogeneousPairs`
- `Langlands.Representation.Induction.InverseTranspose`
- `Langlands.Representation.Induction.NormalCoinvariantKernelProof`
- `Langlands.Representation.Induction.NormalCoinvariantKernelStatement`
- `Langlands.Representation.Induction.NormalCoinvariantMap`
- `Langlands.Representation.Induction.NormalCoinvariantProof`
- `Langlands.Representation.Induction.NormalCoinvariantStatement`
- `Langlands.Representation.Induction.NormalSplitComparison`
- `Langlands.Representation.Induction.NormalizedIntegralForm`
- `Langlands.Representation.Induction.OppositeParabolic`
- `Langlands.Representation.Induction.OppositeProductReversalProof`
- `Langlands.Representation.Induction.OppositeProductReversalStatement`
- `Langlands.Representation.Induction.Parabolic`
- `Langlands.Representation.Induction.PiScalarIntegral`
- `Langlands.Representation.Induction.SingleBlock`
- `Langlands.Representation.Induction.SplitKernelCharacter`
- `Langlands.Representation.Induction.SplitKernelCharacterExtension`
- `Langlands.Representation.Induction.SplitKernelCompact`
- `Langlands.Representation.Induction.SplitKernelCovariance`
- `Langlands.Representation.Induction.SplitKernelEquivariant`
- `Langlands.Representation.Induction.SplitKernelHaarTrivial`
- `Langlands.Representation.Induction.SplitKernelIntegral`
- `Langlands.Representation.Induction.SplitKernelLocalizationData`
- `Langlands.Representation.Induction.SplitKernelSectionAction`
- `Langlands.Representation.Induction.SplitQuotientProof`
- `Langlands.Representation.Induction.SplitQuotientStatement`
- `Langlands.Representation.Induction.SplitStagesCharacterComparison`
- `Langlands.Representation.Induction.SplitStagesCharacterComparisonStatement`
- `Langlands.Representation.Induction.SplitStagesCharacterIntegrand`
- `Langlands.Representation.Induction.SplitStagesComparison`
- `Langlands.Representation.Induction.SplitStagesRetraction`
- `Langlands.Representation.Induction.StructuralStatement`
- `Langlands.Representation.Induction.SurjectivityProof`
- `Langlands.Representation.Induction.SurjectivityStatement`
- `Langlands.Representation.Jacquet.BlockCompressionProof`
- `Langlands.Representation.Jacquet.BlockCompressionStatement`
- `Langlands.Representation.Jacquet.BlockPowerKernelProof`
- `Langlands.Representation.Jacquet.CanonicalLiftBijectivityProof`
- `Langlands.Representation.Jacquet.CanonicalLiftDefinitions`
- `Langlands.Representation.Jacquet.CanonicalLiftGroupTransportProof`
- `Langlands.Representation.Jacquet.CanonicalLiftGroupTransportStatement`
- `Langlands.Representation.Jacquet.CanonicalLiftIntertwinerNaturalityProof`
- `Langlands.Representation.Jacquet.CanonicalLiftIntertwinerNaturalityStatement`
- `Langlands.Representation.Jacquet.CanonicalLiftStatement`
- `Langlands.Representation.Jacquet.CharacterAveraging`
- `Langlands.Representation.Jacquet.CharacterTwistEquiv`
- `Langlands.Representation.Jacquet.Coinvariants`
- `Langlands.Representation.Jacquet.CompactCompressionStableDualityProof`
- `Langlands.Representation.Jacquet.CompactCompressionStableDualityStatement`
- `Langlands.Representation.Jacquet.CompressionStabilizationProof`
- `Langlands.Representation.Jacquet.CompressionStabilizationStatement`
- `Langlands.Representation.Jacquet.ExactProof`
- `Langlands.Representation.Jacquet.ExactStatement`
- `Langlands.Representation.Jacquet.Localization`
- `Langlands.Representation.Jacquet.LocalizationExactnessProof`
- `Langlands.Representation.Jacquet.LocalizationExactnessStatement`
- `Langlands.Representation.Jacquet.LocalizationTower`
- `Langlands.Representation.Jacquet.LocalizationTransport`
- `Langlands.Representation.Jacquet.Normalized`
- `Langlands.Representation.Jacquet.OppositeCanonicalLiftProof`
- `Langlands.Representation.Jacquet.OppositeCanonicalLiftStatement`
- `Langlands.Representation.Jacquet.Parabolic`
- `Langlands.Representation.Jacquet.PositiveCharacter`
- `Langlands.Representation.Jacquet.ReciprocityProof`
- `Langlands.Representation.Jacquet.ReciprocityStatement`
- `Langlands.Representation.Jacquet.RefinedOppositeCanonicalLiftProof`
- `Langlands.Representation.Jacquet.RefinedOppositeCanonicalLiftStatement`
- `Langlands.Representation.Jacquet.RefinedOppositeCompressionProof`
- `Langlands.Representation.Jacquet.RefinedOppositeCompressionStatement`
- `Langlands.Representation.Jacquet.RefinedOppositePowerKernelProof`
- `Langlands.Representation.Jacquet.RefinedOppositeStableImageProof`
- `Langlands.Representation.Jacquet.RefinedUpperCanonicalLiftProof`
- `Langlands.Representation.Jacquet.SmoothTwist`
- `Langlands.Representation.Jacquet.StablePairingProof`
- `Langlands.Representation.MatrixCoefficient.Definitions`
- `Langlands.Representation.MatrixCoefficient.HermitianProduct`
- `Langlands.Representation.MatrixCoefficient.LawsProof`
- `Langlands.Representation.MatrixCoefficient.LawsStatement`
- `Langlands.Representation.MatrixCoefficient.ModuloCenter`
- `Langlands.Representation.MatrixCoefficient.NormRegularityProof`
- `Langlands.Representation.MatrixCoefficient.NormRegularityStatement`
- `Langlands.Representation.Mirabolic.LeftMixedProductSuccessor`
- `Langlands.Representation.Mirabolic.MixedProducts`
- `Langlands.Representation.OrbitSpan`
- `Langlands.Representation.Parabolic.AdmissibilityStatement`
- `Langlands.Representation.Parabolic.ComposedFunctors`
- `Langlands.Representation.Parabolic.ExactnessReciprocityStatement`
- `Langlands.Representation.Parabolic.FlattenedJacquetComparisonProof`
- `Langlands.Representation.Parabolic.FlattenedJacquetComparisonStatement`
- `Langlands.Representation.Parabolic.FlattenedJacquetQuotientProof`
- `Langlands.Representation.Parabolic.FlattenedJacquetQuotientStatement`
- `Langlands.Representation.Parabolic.FlattenedProductInduction`
- `Langlands.Representation.Parabolic.FlattenedRefinementModulusCalculation`
- `Langlands.Representation.Parabolic.FlattenedTensorOccurrences`
- `Langlands.Representation.Parabolic.GeometricPrerequisitesStatement`
- `Langlands.Representation.Parabolic.HeadTailProductInduction`
- `Langlands.Representation.Parabolic.InducedMapSurjectivity`
- `Langlands.Representation.Parabolic.InductionExactnessProof`
- `Langlands.Representation.Parabolic.InductionFactorMatchingProof`
- `Langlands.Representation.Parabolic.InductionFactorMatchingStatement`
- `Langlands.Representation.Parabolic.InductionFiltration`
- `Langlands.Representation.Parabolic.InductionSubrepresentation`
- `Langlands.Representation.Parabolic.InverseTransposeProductProof`
- `Langlands.Representation.Parabolic.InverseTransposeProductStatement`
- `Langlands.Representation.Parabolic.JacquetFiniteGenerationProof`
- `Langlands.Representation.Parabolic.JacquetFiniteGenerationStatement`
- `Langlands.Representation.Parabolic.LeviBridges`
- `Langlands.Representation.Parabolic.LeviInflationAdmissibilityProof`
- `Langlands.Representation.Parabolic.NaturalFirstAdjointness`
- `Langlands.Representation.Parabolic.NaturalInductionDualityFromScalar`
- `Langlands.Representation.Parabolic.NaturalInductionDualityProof`
- `Langlands.Representation.Parabolic.NaturalInductionDualityStatement`
- `Langlands.Representation.Parabolic.NaturalJacquetDualityProof`
- `Langlands.Representation.Parabolic.NaturalJacquetDualityStatement`
- `Langlands.Representation.Parabolic.NormalizedAdmissibilityProof`
- `Langlands.Representation.Parabolic.NormalizedCompatibilityStatement`
- `Langlands.Representation.Parabolic.NormalizedInductionStatement`
- `Langlands.Representation.Parabolic.NormalizedJacquetAdmissibilityProof`
- `Langlands.Representation.Parabolic.NormalizedJacquetExactnessProof`
- `Langlands.Representation.Parabolic.NormalizedJacquetStatement`
- `Langlands.Representation.Parabolic.OppositeJacquetAdmissibilityProof`
- `Langlands.Representation.Parabolic.OppositeJacquetAdmissibilityStatement`
- `Langlands.Representation.Parabolic.OppositeJacquetMap`
- `Langlands.Representation.Parabolic.OppositeRefinementDefinitions`
- `Langlands.Representation.Parabolic.OppositeRefinementFunctors`
- `Langlands.Representation.Parabolic.OppositeRefinementTransitivityProof`
- `Langlands.Representation.Parabolic.OppositeRefinementTransitivityStatement`
- `Langlands.Representation.Parabolic.OrderedProductRegroupingEquivalence`
- `Langlands.Representation.Parabolic.OrderedProductRegroupingProof`
- `Langlands.Representation.Parabolic.OrderedProductRegroupingStatement`
- `Langlands.Representation.Parabolic.OrderedRefinementInduction`
- `Langlands.Representation.Parabolic.OrderedRefinementTensorInduction`
- `Langlands.Representation.Parabolic.ProductInductionFiltration`
- `Langlands.Representation.Parabolic.ProductInductionSubrepresentation`
- `Langlands.Representation.Parabolic.QuotientCompactProof`
- `Langlands.Representation.Parabolic.RefinedInductionAdmissibility`
- `Langlands.Representation.Parabolic.RefinedInductionTensorMap`
- `Langlands.Representation.Parabolic.RefinedInductionTensorNormalization`
- `Langlands.Representation.Parabolic.RefinedInductionTensorProof`
- `Langlands.Representation.Parabolic.RefinedInductionTensorStatement`
- `Langlands.Representation.Parabolic.RefinedJacquetTensor`
- `Langlands.Representation.Parabolic.RefinedOppositeJacquetTensor`
- `Langlands.Representation.Parabolic.RefinedTensorOccurrences`
- `Langlands.Representation.Parabolic.RefinementCharacter`
- `Langlands.Representation.Parabolic.RefinementComposition`
- `Langlands.Representation.Parabolic.RefinementCoordinatesNormalizationProof`
- `Langlands.Representation.Parabolic.RefinementCoordinatesNormalizationStatement`
- `Langlands.Representation.Parabolic.RefinementInductionTransitivityProof`
- `Langlands.Representation.Parabolic.RefinementJacquetTransitivityProof`
- `Langlands.Representation.Parabolic.RefinementPreimage`
- `Langlands.Representation.Parabolic.RefinementTransitivityStatement`
- `Langlands.Representation.Parabolic.RegroupingFactorEquivalences`
- `Langlands.Representation.Parabolic.SecondAdjointnessAssembly`
- `Langlands.Representation.Parabolic.SecondAdjointnessProof`
- `Langlands.Representation.Parabolic.SecondAdjointnessStatement`
- `Langlands.Representation.Parabolic.StandardOppositeJacquetAdmissibilityProof`
- `Langlands.Representation.Parabolic.ThreeBlockCarrierComparison`
- `Langlands.Representation.Parabolic.ThreeBlockInductionAssociativityStatement`
- `Langlands.Representation.Parabolic.ThreeBlockRefinementGeometry`
- `Langlands.Representation.Parabolic.ThreeBlockRegroupingAssembly`
- `Langlands.Representation.Parabolic.ThreeBlockUniverseReduction`
- `Langlands.Representation.Parabolic.UnipotentFiniteContainment`
- `Langlands.Representation.RankinSelberg.AnalyticStatement`
- `Langlands.Representation.RankinSelberg.EqualRankFrobeniusProof`
- `Langlands.Representation.RankinSelberg.EqualRankFrobeniusStatement`
- `Langlands.Representation.RankinSelberg.EqualRankTrilinearAssembly`
- `Langlands.Representation.RankinSelberg.EqualRankTrilinearReduction`
- `Langlands.Representation.RankinSelberg.EqualRankTrilinearUniquenessStatement`
- `Langlands.Representation.RankinSelberg.FunctionalEquationStatement`
- `Langlands.Representation.RankinSelberg.GeneralLinearUnimodularity`
- `Langlands.Representation.RankinSelberg.HaarSymmetriesProof`
- `Langlands.Representation.RankinSelberg.HaarSymmetriesStatement`
- `Langlands.Representation.RankinSelberg.LastRowCompactOrbitProof`
- `Langlands.Representation.RankinSelberg.LastRowCompactOrbitStatement`
- `Langlands.Representation.RankinSelberg.LocalFactor`
- `Langlands.Representation.RankinSelberg.Measures`
- `Langlands.Representation.RankinSelberg.QuotientIntegrals`
- `Langlands.Representation.RankinSelberg.RankOneQuotient`
- `Langlands.Representation.RankinSelberg.RationalContinuation`
- `Langlands.Representation.RankinSelberg.RationalZeta`
- `Langlands.Representation.RankinSelberg.TwistInvariance`
- `Langlands.Representation.RankinSelberg.UnimodularityStatement`
- `Langlands.Representation.RankinSelberg.UnipotentQuotient`
- `Langlands.Representation.RankinSelberg.UnipotentUnimodularity`
- `Langlands.Representation.RankinSelberg.ZeroRowLastRowCutoffProof`
- `Langlands.Representation.RankinSelberg.ZeroRowLastRowCutoffStatement`
- `Langlands.Representation.Schur.CountableDimensionProof`
- `Langlands.Representation.Schur.CountableDimensionStatement`
- `Langlands.Representation.Shahidi.Geometry`
- `Langlands.Representation.Shahidi.Induction`
- `Langlands.Representation.Shahidi.IntertwiningCovariance`
- `Langlands.Representation.Shahidi.IntertwiningInduced`
- `Langlands.Representation.Shahidi.IntertwiningIntegral`
- `Langlands.Representation.Shahidi.TwoBlocks`
- `Langlands.Representation.Smooth.Admissibility.CofinalProof`
- `Langlands.Representation.Smooth.Admissibility.CofinalStatement`
- `Langlands.Representation.Smooth.Admissibility.EmbeddingProof`
- `Langlands.Representation.Smooth.Admissibility.EmbeddingStatement`
- `Langlands.Representation.Smooth.Admissibility.EquivalenceProof`
- `Langlands.Representation.Smooth.Admissibility.EquivalenceStatement`
- `Langlands.Representation.Smooth.Admissibility.ExactProof`
- `Langlands.Representation.Smooth.Admissibility.ExactStatement`
- `Langlands.Representation.Smooth.Admissibility.Extension`
- `Langlands.Representation.Smooth.Admissibility.FiniteLengthProof`
- `Langlands.Representation.Smooth.Admissibility.FiniteLengthStatement`
- `Langlands.Representation.Smooth.Contragredient.AdmissibleDualityProof`
- `Langlands.Representation.Smooth.Contragredient.AdmissibleDualityStatement`
- `Langlands.Representation.Smooth.Contragredient.CompactDualityProof`
- `Langlands.Representation.Smooth.Contragredient.CompactDualityStatement`
- `Langlands.Representation.Smooth.Contragredient.Definitions`
- `Langlands.Representation.Smooth.Contragredient.ExactProof`
- `Langlands.Representation.Smooth.Contragredient.ExactStatement`
- `Langlands.Representation.Smooth.Contragredient.FixedVectorsDefinitions`
- `Langlands.Representation.Smooth.Contragredient.GelfandKazhdanAssembly`
- `Langlands.Representation.Smooth.Contragredient.GelfandKazhdanProof`
- `Langlands.Representation.Smooth.Contragredient.GelfandKazhdanStatement`
- `Langlands.Representation.Smooth.Contragredient.HomDualityProof`
- `Langlands.Representation.Smooth.Contragredient.HomDualityStatement`
- `Langlands.Representation.Smooth.Contragredient.InvariantPairingProof`
- `Langlands.Representation.Smooth.Contragredient.InvariantPairingStatement`
- `Langlands.Representation.Smooth.Contragredient.LawsProof`
- `Langlands.Representation.Smooth.Contragredient.LawsStatement`
- `Langlands.Representation.Smooth.Definitions`
- `Langlands.Representation.Smooth.Factorization.MultiplicityDefinitions`
- `Langlands.Representation.Smooth.Factorization.TwoFactorExistenceProof`
- `Langlands.Representation.Smooth.Factorization.TwoFactorStatement`
- `Langlands.Representation.Smooth.FiniteLengthGrothendieck`
- `Langlands.Representation.Smooth.FixedVectors.Definitions`
- `Langlands.Representation.Smooth.FixedVectors.Detection`
- `Langlands.Representation.Smooth.FixedVectors.FiniteTypes`
- `Langlands.Representation.Smooth.FixedVectors.FiniteTypesStatement`
- `Langlands.Representation.Smooth.FixedVectors.GenerationInheritance`
- `Langlands.Representation.Smooth.FixedVectors.GenerationInheritanceStatement`
- `Langlands.Representation.Smooth.FixedVectors.LawsProof`
- `Langlands.Representation.Smooth.FixedVectors.LawsStatement`
- `Langlands.Representation.Smooth.FixedVectors.OrderProof`
- `Langlands.Representation.Smooth.FixedVectors.OrderStatement`
- `Langlands.Representation.Smooth.Schur.Proof`
- `Langlands.Representation.Smooth.Schur.Statement`
- `Langlands.Representation.Smooth.SmallRealizationProof`
- `Langlands.Representation.Smooth.SmallRealizationStatement`
- `Langlands.Representation.Smooth.SmoothPart.BasicProof`
- `Langlands.Representation.Smooth.SmoothPart.BasicStatement`
- `Langlands.Representation.Smooth.SmoothPart.Definitions`
- `Langlands.Representation.Smooth.SmoothPart.FixedVectorsDefinitions`
- `Langlands.Representation.Smooth.Transfer.GroupEquivalence`
- `Langlands.Representation.Smooth.Transfer.PullbackProof`
- `Langlands.Representation.Smooth.Transfer.PullbackStatement`
- `Langlands.Representation.Smooth.Transfer.SubquotientProof`
- `Langlands.Representation.Smooth.Transfer.SubquotientStatement`
- `Langlands.Representation.SubrepresentationLattice`
- `Langlands.Representation.Tensor.CharacterLocalization`
- `Langlands.Representation.Tensor.CoinvariantReflection`
- `Langlands.Representation.Tensor.ExternalFiltration`
- `Langlands.Representation.Tensor.ExternalMapSurjectivityProof`
- `Langlands.Representation.Tensor.ExternalMapSurjectivityStatement`
- `Langlands.Representation.Tensor.ExternalSubquotient`
- `Langlands.Representation.Tensor.ExternalSubrepresentation`
- `Langlands.Representation.Tensor.FactorMatchingProof`
- `Langlands.Representation.Tensor.FactorMatchingStatement`
- `Langlands.Representation.Tensor.Filtration`
- `Langlands.Representation.Tensor.Finite`
- `Langlands.Representation.Tensor.FiniteEquivalences`
- `Langlands.Representation.Tensor.FiniteFiltration`
- `Langlands.Representation.Tensor.FiniteProperties`
- `Langlands.Representation.Tensor.FiniteRegrouping`
- `Langlands.Representation.Tensor.FlattenedGLRefinement`
- `Langlands.Representation.Tensor.GLRefinement`
- `Langlands.Representation.Tensor.OneFactor`
- `Langlands.Representation.Tensor.ProductFiltration`
- `Langlands.Representation.Tensor.SmoothDual`
- `Langlands.Representation.Tensor.SmoothDualInjectivityProof`
- `Langlands.Representation.Tensor.SmoothDualInjectivityStatement`
- `Langlands.Representation.Tensor.SmoothDualSurjectivityProof`
- `Langlands.Representation.Tensor.SmoothDualSurjectivityStatement`
- `Langlands.Representation.Tensor.SmoothSubquotients`
- `Langlands.Representation.Tensor.UnitaryProof`
- `Langlands.Representation.Tensor.UnitaryStatement`
- `Langlands.Representation.Twist.AdmissibilityProof`
- `Langlands.Representation.Twist.AdmissibilityStatement`
- `Langlands.Representation.Twist.AlgebraProof`
- `Langlands.Representation.Twist.AlgebraStatement`
- `Langlands.Representation.Twist.ContinuousCharacterProof`
- `Langlands.Representation.Twist.ContinuousCharacterStatement`
- `Langlands.Representation.Twist.Definitions`
- `Langlands.Representation.Twist.DualProof`
- `Langlands.Representation.Twist.DualStatement`
- `Langlands.Representation.Twist.LeviComplexPower`
- `Langlands.Representation.Twist.LeviRealPower`
- `Langlands.Representation.Twist.PullbackProof`
- `Langlands.Representation.Twist.PullbackStatement`
- `Langlands.Representation.Twist.RealPower`
- `Langlands.Representation.Twist.SmoothPartDefinitions`
- `Langlands.Representation.Twist.SmoothProof`
- `Langlands.Representation.Twist.SmoothStatement`
- `Langlands.Representation.Twist.SubquotientDefinitions`
- `Langlands.Representation.Twist.SubquotientProof`
- `Langlands.Representation.Twist.SubquotientStatement`
- `Langlands.Representation.Unitary.Basic`
- `Langlands.Representation.Unitary.CentralCharacterProof`
- `Langlands.Representation.Unitary.CentralCharacterStatement`
- `Langlands.Representation.Unitary.HermitianDual`
- `Langlands.Representation.Unitary.LeviCuspidalRealUnitarizationProof`
- `Langlands.Representation.Unitary.LeviCuspidalRealUnitarizationStatement`
- `Langlands.Representation.Unitary.SquareIntegrableProof`
- `Langlands.Representation.Unitary.SquareIntegrableStatement`
- `Langlands.Representation.Unitary.SupercuspidalRealUnitarizationProof`
- `Langlands.Representation.Unitary.SupercuspidalRealUnitarizationStatement`
- `Langlands.Representation.Unitary.Twist`
- `Langlands.Representation.Unitary.UnitarizabilityContinuationProof`
- `Langlands.Representation.Unitary.UnitarizabilityContinuationStatement`
- `Langlands.Representation.Unramified.Eigenvalues`
- `Langlands.Representation.Unramified.HeckeOperators`
- `Langlands.Representation.Unramified.PrincipalSeries`
- `Langlands.Representation.Unramified.SphericalClassificationStatement`
- `Langlands.Representation.Unramified.SphericalConstituentExistenceProof`
- `Langlands.Representation.Whittaker.Algebraic`
- `Langlands.Representation.Whittaker.AlgebraicTwist`
- `Langlands.Representation.Whittaker.BruhatCellDistribution`
- `Langlands.Representation.Whittaker.BruhatCellFactorizationProof`
- `Langlands.Representation.Whittaker.BruhatCellFactorizationStatement`
- `Langlands.Representation.Whittaker.BruhatCellInvarianceProof`
- `Langlands.Representation.Whittaker.BruhatCellInvarianceStatement`
- `Langlands.Representation.Whittaker.BruhatCellRestrictionVanishingProof`
- `Langlands.Representation.Whittaker.BruhatCellRestrictionVanishingStatement`
- `Langlands.Representation.Whittaker.BruhatCellVanishingProof`
- `Langlands.Representation.Whittaker.BruhatCellVanishingStatement`
- `Langlands.Representation.Whittaker.BruhatCompatibleSupportProof`
- `Langlands.Representation.Whittaker.BruhatCompatibleSupportStatement`
- `Langlands.Representation.Whittaker.BruhatFiberAverage`
- `Langlands.Representation.Whittaker.BruhatFiberCharacterCovarianceProof`
- `Langlands.Representation.Whittaker.BruhatFiberCharacterCovarianceStatement`
- `Langlands.Representation.Whittaker.BruhatHaarMeasureProof`
- `Langlands.Representation.Whittaker.BruhatHaarMeasureStatement`
- `Langlands.Representation.Whittaker.BruhatOrbitalIntegrationProof`
- `Langlands.Representation.Whittaker.BruhatOrbitalIntegrationStatement`
- `Langlands.Representation.Whittaker.BundledDualTransport`
- `Langlands.Representation.Whittaker.CharacterChange`
- `Langlands.Representation.Whittaker.CoefficientDistribution`
- `Langlands.Representation.Whittaker.CompatibleMonomialFixedProof`
- `Langlands.Representation.Whittaker.CompatibleMonomialFixedStatement`
- `Langlands.Representation.Whittaker.CompatibleTorus`
- `Langlands.Representation.Whittaker.Distribution`
- `Langlands.Representation.Whittaker.DistributionInvarianceProof`
- `Langlands.Representation.Whittaker.DistributionInvarianceStatement`
- `Langlands.Representation.Whittaker.DualTransform`
- `Langlands.Representation.Whittaker.EntrywiseCharacter`
- `Langlands.Representation.Whittaker.GeneralLinear`
- `Langlands.Representation.Whittaker.GeneralizedCoefficient`
- `Langlands.Representation.Whittaker.GeneralizedCoefficientDescent`
- `Langlands.Representation.Whittaker.GeneralizedCoefficientKernelProof`
- `Langlands.Representation.Whittaker.GeneralizedCoefficientKernelStatement`
- `Langlands.Representation.Whittaker.GeneralizedCoefficientSeparation`
- `Langlands.Representation.Whittaker.GenericDualTransport`
- `Langlands.Representation.Whittaker.Iwasawa`
- `Langlands.Representation.Whittaker.MirabolicQuotientMeasure`
- `Langlands.Representation.Whittaker.MultiplicityOneProof`
- `Langlands.Representation.Whittaker.MultiplicityOneStatement`
- `Langlands.Representation.Whittaker.PrerequisiteInterfaces`
- `Langlands.Representation.Whittaker.PrerequisitesStatement`
- `Langlands.Representation.Whittaker.Twist`
- `Langlands.Topology.CompactNormCharacter`
- `Langlands.Topology.CompactOpen.ConjugationStabilizer`
- `Langlands.Topology.CompactOpen.NeighborhoodBasis`
- `Langlands.Topology.CompactOpen.NeighborhoodBasisStatement`
- `Langlands.Topology.GroupAction.FiniteOrbitProof`
- `Langlands.Topology.GroupAction.FiniteOrbitStatement`
- `Langlands.Topology.Nonarchimedean.Subgroup`
- `Langlands.VirtualRepresentation.Exact`
- `Langlands.VirtualRepresentation.ExactTwist`
- `Langlands.VirtualRepresentation.Integral`
- `Langlands.Weil.Algebraic`
- `Langlands.Weil.AlgebraicProof`
- `Langlands.Weil.Local.Assembly`
- `Langlands.Weil.Local.DegreeCharacters`
- `Langlands.Weil.Local.Parameters`
- `Langlands.Weil.Local.ResidueCharacters`
- `Langlands.Weil.Pullback`
- `Langlands.Weil.Representation.Basic`
- `Langlands.Weil.Representation.CharacterLine`
- `Langlands.Weil.Representation.Continuity`
- `Langlands.Weil.Representation.ContinuityProof`
- `Langlands.Weil.Representation.Determinant`
- `Langlands.Weil.Representation.DirectSum`
- `Langlands.Weil.Representation.Dual`
- `Langlands.Weil.Representation.DualClasses`
- `Langlands.Weil.Representation.IsomorphismInvarianceProof`
- `Langlands.Weil.Representation.OperationClosureProof`
- `Langlands.Weil.Representation.Operations`
- `Langlands.Weil.Representation.Predicates`
- `Langlands.Weil.Representation.Twist`
- `Langlands.Weil.Representation.TwistClasses`
- `Langlands.Weil.Representation.TwistProperties`
- `Langlands.Weil.Topology`
- `Langlands.Weil.TopologyProof`
- `Langlands.WeilDeligne.Basic`
- `Langlands.WeilDeligne.DirectSum`
- `Langlands.WeilDeligne.Dual`
- `Langlands.WeilDeligne.ParameterRelations`
- `Langlands.WeilDeligne.Parameters`
- `Langlands.WeilDeligne.Twist`

## External import roots

- `Lean.Elab.Tactic.Omega`
- `Mathlib.Algebra.Algebra.Bilinear`
- `Mathlib.Algebra.Algebra.NonUnitalHom`
- `Mathlib.Algebra.Algebra.NonUnitalSubalgebra`
- `Mathlib.Algebra.Algebra.Subalgebra.Lattice`
- `Mathlib.Algebra.BigOperators.Fin`
- `Mathlib.Algebra.BigOperators.Finprod`
- `Mathlib.Algebra.BigOperators.Group.Finset.Basic`
- `Mathlib.Algebra.BigOperators.Group.List.Basic`
- `Mathlib.Algebra.BigOperators.Group.Multiset.Basic`
- `Mathlib.Algebra.BigOperators.GroupWithZero.Action`
- `Mathlib.Algebra.BigOperators.Pi`
- `Mathlib.Algebra.Category.ModuleCat.Basic`
- `Mathlib.Algebra.CharP.Basic`
- `Mathlib.Algebra.DirectSum.Module`
- `Mathlib.Algebra.Exact.Basic`
- `Mathlib.Algebra.Field.Subfield.Basic`
- `Mathlib.Algebra.Group.Action.Hom`
- `Mathlib.Algebra.Group.Action.Opposite`
- `Mathlib.Algebra.Group.AddChar`
- `Mathlib.Algebra.Group.Equiv.TypeTags`
- `Mathlib.Algebra.Group.Hom.Instances`
- `Mathlib.Algebra.Group.Pi.Lemmas`
- `Mathlib.Algebra.Group.Subgroup.Ker`
- `Mathlib.Algebra.Group.Subgroup.Pointwise`
- `Mathlib.Algebra.Group.Submonoid.Basic`
- `Mathlib.Algebra.Group.TypeTags.Finite`
- `Mathlib.Algebra.Group.TypeTags.Hom`
- `Mathlib.Algebra.Module.CharacterModule`
- `Mathlib.Algebra.Module.LinearMap.FiniteRange`
- `Mathlib.Algebra.Module.Opposite`
- `Mathlib.Algebra.Module.PID`
- `Mathlib.Algebra.Module.Projective`
- `Mathlib.Algebra.Module.Submodule.Map`
- `Mathlib.Algebra.Module.ULift`
- `Mathlib.Algebra.Order.Archimedean.Basic`
- `Mathlib.Algebra.Order.BigOperators.Group.Finset`
- `Mathlib.Algebra.Polynomial.FieldDivision`
- `Mathlib.Algebra.Polynomial.Laurent`
- `Mathlib.Algebra.Polynomial.Lifts`
- `Mathlib.Algebra.Polynomial.Module.AEval`
- `Mathlib.Algebra.Polynomial.Module.FiniteDimensional`
- `Mathlib.Algebra.Polynomial.Roots`
- `Mathlib.Algebra.Ring.GeomSum`
- `Mathlib.Analysis.Complex.Basic`
- `Mathlib.Analysis.Complex.Cardinality`
- `Mathlib.Analysis.Complex.Circle`
- `Mathlib.Analysis.Complex.Polynomial.Basic`
- `Mathlib.Analysis.Fourier.FourierTransform`
- `Mathlib.Analysis.InnerProductSpace.Defs`
- `Mathlib.Analysis.InnerProductSpace.Dual`
- `Mathlib.Analysis.InnerProductSpace.TensorProduct`
- `Mathlib.Analysis.Matrix.Hermitian`
- `Mathlib.Analysis.Matrix.MeasurableSpace`
- `Mathlib.Analysis.Matrix.Normed`
- `Mathlib.Analysis.MeanInequalitiesPow`
- `Mathlib.Analysis.Normed.Module.FiniteDimension`
- `Mathlib.Analysis.Normed.Operator.BoundedLinearMaps`
- `Mathlib.Analysis.Normed.Unbundled.SpectralNorm`
- `Mathlib.Analysis.Real.Sqrt`
- `Mathlib.Analysis.SpecialFunctions.Complex.Circle`
- `Mathlib.Analysis.SpecialFunctions.Log.Base`
- `Mathlib.Analysis.SpecialFunctions.Pow.Complex`
- `Mathlib.Analysis.SpecialFunctions.Pow.Continuity`
- `Mathlib.Analysis.SpecialFunctions.Pow.NNReal`
- `Mathlib.Analysis.SpecialFunctions.Pow.Real`
- `Mathlib.Analysis.SpecialFunctions.Sqrt`
- `Mathlib.Analysis.SpecificLimits.Basic`
- `Mathlib.Basic.Complex.Basic`
- `Mathlib.CategoryTheory.Abelian.Subcategory`
- `Mathlib.CategoryTheory.Discrete.Basic`
- `Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic`
- `Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero`
- `Mathlib.CategoryTheory.ObjectProperty.FullSubcategory`
- `Mathlib.CategoryTheory.Pi.Basic`
- `Mathlib.CategoryTheory.Preadditive.AdditiveFunctor`
- `Mathlib.CategoryTheory.Products.Basic`
- `Mathlib.CategoryTheory.Skeletal`
- `Mathlib.CategoryTheory.Whiskering`
- `Mathlib.Combinatorics.Enumerative.Composition`
- `Mathlib.Data.ENat.Basic`
- `Mathlib.Data.ENat.BigOperators`
- `Mathlib.Data.Fin.Rev`
- `Mathlib.Data.Fin.Tuple.Basic`
- `Mathlib.Data.Fin.Tuple.Sort`
- `Mathlib.Data.Finset.NatAntidiagonal`
- `Mathlib.Data.Fintype.EquivFin`
- `Mathlib.Data.Fintype.Quotient`
- `Mathlib.Data.Fintype.Sort`
- `Mathlib.Data.Fintype.Sum`
- `Mathlib.Data.Int.Cast.Lemmas`
- `Mathlib.Data.Int.Interval`
- `Mathlib.Data.Int.LeastGreatest`
- `Mathlib.Data.List.Pairwise`
- `Mathlib.Data.Matrix.Basic`
- `Mathlib.Data.Matrix.Block`
- `Mathlib.Data.Nat.Find`
- `Mathlib.Data.PNat.Basic`
- `Mathlib.Data.Set.Card`
- `Mathlib.Data.Set.Finite.Basic`
- `Mathlib.Data.Sym.Basic`
- `Mathlib.Data.ZMod.Basic`
- `Mathlib.FieldTheory.AbsoluteGaloisGroup`
- `Mathlib.FieldTheory.Finite.Basic`
- `Mathlib.FieldTheory.Finite.Extension`
- `Mathlib.FieldTheory.Galois.Profinite`
- `Mathlib.FieldTheory.PrimitiveElement`
- `Mathlib.FieldTheory.RatFunc.AsPolynomial`
- `Mathlib.GroupTheory.Abelianization.Defs`
- `Mathlib.GroupTheory.Coset.Defs`
- `Mathlib.GroupTheory.DoubleCoset`
- `Mathlib.GroupTheory.FiniteIndexNormalSubgroup`
- `Mathlib.GroupTheory.GroupAction.Basic`
- `Mathlib.GroupTheory.GroupAction.ConjAct`
- `Mathlib.GroupTheory.GroupAction.Defs`
- `Mathlib.GroupTheory.GroupAction.Quotient`
- `Mathlib.GroupTheory.Index`
- `Mathlib.GroupTheory.OrderOfElement`
- `Mathlib.GroupTheory.QuotientGroup.Defs`
- `Mathlib.GroupTheory.Subgroup.Center`
- `Mathlib.GroupTheory.Subgroup.Centralizer`
- `Mathlib.GroupTheory.Transfer`
- `Mathlib.LinearAlgebra.AffineSpace.AffineMap`
- `Mathlib.LinearAlgebra.AnnihilatingPolynomial`
- `Mathlib.LinearAlgebra.Basis.VectorSpace`
- `Mathlib.LinearAlgebra.BilinearForm.Properties`
- `Mathlib.LinearAlgebra.BilinearMap`
- `Mathlib.LinearAlgebra.Charpoly.Basic`
- `Mathlib.LinearAlgebra.Charpoly.ToMatrix`
- `Mathlib.LinearAlgebra.Determinant`
- `Mathlib.LinearAlgebra.Dimension.Basic`
- `Mathlib.LinearAlgebra.Dimension.Constructions`
- `Mathlib.LinearAlgebra.Dimension.StrongRankCondition`
- `Mathlib.LinearAlgebra.DirectSum.Finite`
- `Mathlib.LinearAlgebra.Dual.Defs`
- `Mathlib.LinearAlgebra.Dual.Lemmas`
- `Mathlib.LinearAlgebra.Eigenspace.Basic`
- `Mathlib.LinearAlgebra.Eigenspace.Pi`
- `Mathlib.LinearAlgebra.Eigenspace.Triangularizable`
- `Mathlib.LinearAlgebra.FiniteDimensional.Basic`
- `Mathlib.LinearAlgebra.FiniteDimensional.Defs`
- `Mathlib.LinearAlgebra.FiniteDimensional.Lemmas`
- `Mathlib.LinearAlgebra.Finsupp.LinearCombination`
- `Mathlib.LinearAlgebra.Finsupp.VectorSpace`
- `Mathlib.LinearAlgebra.FreeModule.Finite.Matrix`
- `Mathlib.LinearAlgebra.Isomorphisms`
- `Mathlib.LinearAlgebra.Matrix.BilinearForm`
- `Mathlib.LinearAlgebra.Matrix.Block`
- `Mathlib.LinearAlgebra.Matrix.Charpoly.Basic`
- `Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff`
- `Mathlib.LinearAlgebra.Matrix.Charpoly.Univ`
- `Mathlib.LinearAlgebra.Matrix.Diagonal`
- `Mathlib.LinearAlgebra.Matrix.ElementaryRowOperations`
- `Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic`
- `Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs`
- `Mathlib.LinearAlgebra.Matrix.Kronecker`
- `Mathlib.LinearAlgebra.Matrix.NonsingularInverse`
- `Mathlib.LinearAlgebra.Matrix.Permutation`
- `Mathlib.LinearAlgebra.Matrix.PosDef`
- `Mathlib.LinearAlgebra.Matrix.Rank`
- `Mathlib.LinearAlgebra.Matrix.Reindex`
- `Mathlib.LinearAlgebra.Matrix.SchurComplement`
- `Mathlib.LinearAlgebra.Matrix.ToLinearEquiv`
- `Mathlib.LinearAlgebra.Matrix.Transvection`
- `Mathlib.LinearAlgebra.PiTensorProduct.Basic`
- `Mathlib.LinearAlgebra.PiTensorProduct.Basis`
- `Mathlib.LinearAlgebra.PiTensorProduct.Dual`
- `Mathlib.LinearAlgebra.PiTensorProduct.Finite`
- `Mathlib.LinearAlgebra.PiTensorProduct.Generators`
- `Mathlib.LinearAlgebra.Projection`
- `Mathlib.LinearAlgebra.Quotient.Basic`
- `Mathlib.LinearAlgebra.Semisimple`
- `Mathlib.LinearAlgebra.TensorProduct.Basis`
- `Mathlib.LinearAlgebra.TensorProduct.Finiteness`
- `Mathlib.LinearAlgebra.TensorProduct.RightExactness`
- `Mathlib.LinearAlgebra.Trace`
- `Mathlib.Logic.Equiv.Fin.Basic`
- `Mathlib.MeasureTheory.Constructions.BorelSpace.Complex`
- `Mathlib.MeasureTheory.Constructions.Pi`
- `Mathlib.MeasureTheory.Function.L2Space`
- `Mathlib.MeasureTheory.Function.LocallyIntegrable`
- `Mathlib.MeasureTheory.Function.LpSeminorm.Defs`
- `Mathlib.MeasureTheory.Function.LpSpace.Indicator`
- `Mathlib.MeasureTheory.Function.SimpleFunc`
- `Mathlib.MeasureTheory.Group.Integral`
- `Mathlib.MeasureTheory.Group.LIntegral`
- `Mathlib.MeasureTheory.Group.MeasurableEquiv`
- `Mathlib.MeasureTheory.Group.Measure`
- `Mathlib.MeasureTheory.Group.ModularCharacter`
- `Mathlib.MeasureTheory.Integral.Bochner.Basic`
- `Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap`
- `Mathlib.MeasureTheory.Integral.Bochner.Set`
- `Mathlib.MeasureTheory.Integral.Marginal`
- `Mathlib.MeasureTheory.Integral.Prod`
- `Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real`
- `Mathlib.MeasureTheory.Measure.Haar.Basic`
- `Mathlib.MeasureTheory.Measure.Haar.DistribChar`
- `Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar`
- `Mathlib.MeasureTheory.Measure.Haar.Unique`
- `Mathlib.MeasureTheory.Measure.Lebesgue.Basic`
- `Mathlib.MeasureTheory.Measure.OpenPos`
- `Mathlib.MeasureTheory.Measure.Prod`
- `Mathlib.MeasureTheory.Measure.Regular`
- `Mathlib.MeasureTheory.Measure.Typeclasses.Finite`
- `Mathlib.NumberTheory.LocalField.Basic`
- `Mathlib.NumberTheory.Padics.LocalField`
- `Mathlib.NumberTheory.Padics.RingHoms`
- `Mathlib.Order.Atoms`
- `Mathlib.Order.CompactlyGenerated.Basic`
- `Mathlib.Order.Hom.Set`
- `Mathlib.Order.Interval.Finset.Fin`
- `Mathlib.Order.Interval.Set.Infinite`
- `Mathlib.Order.WithBot`
- `Mathlib.RepresentationTheory.Basic`
- `Mathlib.RepresentationTheory.Coinduced`
- `Mathlib.RepresentationTheory.Coinvariants`
- `Mathlib.RepresentationTheory.Equiv`
- `Mathlib.RepresentationTheory.Intertwining`
- `Mathlib.RepresentationTheory.Invariants`
- `Mathlib.RepresentationTheory.Irreducible`
- `Mathlib.RepresentationTheory.Rep.Basic`
- `Mathlib.RepresentationTheory.Rep.Res`
- `Mathlib.RepresentationTheory.Semisimple`
- `Mathlib.RepresentationTheory.Subrepresentation`
- `Mathlib.RingTheory.Adjoin.Basic`
- `Mathlib.RingTheory.Adjoin.Polynomial.Basic`
- `Mathlib.RingTheory.AdjoinRoot`
- `Mathlib.RingTheory.Algebraic.LinearIndependent`
- `Mathlib.RingTheory.Artinian.Module`
- `Mathlib.RingTheory.DedekindDomain.IntegralClosure`
- `Mathlib.RingTheory.FiniteLength`
- `Mathlib.RingTheory.Finiteness.Basic`
- `Mathlib.RingTheory.Finiteness.Defs`
- `Mathlib.RingTheory.Finiteness.Finsupp`
- `Mathlib.RingTheory.Flat.Basic`
- `Mathlib.RingTheory.FractionalIdeal.Operations`
- `Mathlib.RingTheory.Ideal.Quotient.Basic`
- `Mathlib.RingTheory.Ideal.Quotient.Operations`
- `Mathlib.RingTheory.Jacobson.Semiprimary`
- `Mathlib.RingTheory.Length`
- `Mathlib.RingTheory.Localization.Ideal`
- `Mathlib.RingTheory.Nakayama`
- `Mathlib.RingTheory.Nilpotent.Basic`
- `Mathlib.RingTheory.Noetherian.Basic`
- `Mathlib.RingTheory.Noetherian.Defs`
- `Mathlib.RingTheory.Norm.Transitivity`
- `Mathlib.RingTheory.Polynomial.Basic`
- `Mathlib.RingTheory.Polynomial.UniqueFactorization`
- `Mathlib.RingTheory.PowerBasis`
- `Mathlib.RingTheory.PrincipalIdealDomain`
- `Mathlib.RingTheory.RamificationInertia.Basic`
- `Mathlib.RingTheory.SimpleModule.Basic`
- `Mathlib.RingTheory.SimpleModule.Rank`
- `Mathlib.RingTheory.Trace.Basic`
- `Mathlib.RingTheory.Valuation.Extension`
- `Mathlib.RingTheory.Valuation.Integral`
- `Mathlib.RingTheory.Valuation.LocalSubring`
- `Mathlib.RingTheory.Valuation.RamificationGroup`
- `Mathlib.Tactic`
- `Mathlib.Tactic.Group`
- `Mathlib.Tactic.Linarith`
- `Mathlib.Tactic.LinearCombination`
- `Mathlib.Tactic.NoncommRing`
- `Mathlib.Tactic.NormNum`
- `Mathlib.Tactic.Ring`
- `Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic`
- `Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion`
- `Mathlib.Topology.Algebra.ClopenNhdofOne`
- `Mathlib.Topology.Algebra.ConstMulAction`
- `Mathlib.Topology.Algebra.Constructions`
- `Mathlib.Topology.Algebra.ContinuousMonoidHom`
- `Mathlib.Topology.Algebra.Field`
- `Mathlib.Topology.Algebra.Group.Basic`
- `Mathlib.Topology.Algebra.Group.ClosedSubgroup`
- `Mathlib.Topology.Algebra.Group.Matrix`
- `Mathlib.Topology.Algebra.Group.Neighborhood`
- `Mathlib.Topology.Algebra.Group.OpenMapping`
- `Mathlib.Topology.Algebra.Group.Pointwise`
- `Mathlib.Topology.Algebra.Group.Quotient`
- `Mathlib.Topology.Algebra.Group.Subgroup`
- `Mathlib.Topology.Algebra.Group.Units`
- `Mathlib.Topology.Algebra.GroupWithZero`
- `Mathlib.Topology.Algebra.Module.FiniteDimension`
- `Mathlib.Topology.Algebra.Module.ModuleTopology`
- `Mathlib.Topology.Algebra.MulAction`
- `Mathlib.Topology.Algebra.MvPolynomial`
- `Mathlib.Topology.Algebra.Nonarchimedean.Basic`
- `Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected`
- `Mathlib.Topology.Algebra.OpenSubgroup`
- `Mathlib.Topology.Algebra.ProperAction.Basic`
- `Mathlib.Topology.Algebra.Ring.Compact`
- `Mathlib.Topology.Algebra.Ring.Ideal`
- `Mathlib.Topology.Algebra.Support`
- `Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology`
- `Mathlib.Topology.Algebra.Valued.NormedValued`
- `Mathlib.Topology.Baire.Lemmas`
- `Mathlib.Topology.Baire.LocallyCompactRegular`
- `Mathlib.Topology.Bases`
- `Mathlib.Topology.Compactness.Compact`
- `Mathlib.Topology.Compactness.LocallyCompact`
- `Mathlib.Topology.Compactness.SigmaCompact`
- `Mathlib.Topology.Connected.Clopen`
- `Mathlib.Topology.Connected.TotallyDisconnected`
- `Mathlib.Topology.ContinuousMap.CompactlySupported`
- `Mathlib.Topology.Homeomorph.Defs`
- `Mathlib.Topology.Homeomorph.Lemmas`
- `Mathlib.Topology.Homeomorph.Quotient`
- `Mathlib.Topology.Instances.Int`
- `Mathlib.Topology.Instances.Matrix`
- `Mathlib.Topology.Instances.NNReal.Lemmas`
- `Mathlib.Topology.Instances.Real.Lemmas`
- `Mathlib.Topology.LocallyClosed`
- `Mathlib.Topology.LocallyConstant.Algebra`
- `Mathlib.Topology.LocallyConstant.Basic`
- `Mathlib.Topology.MetricSpace.ProperSpace`
- `Mathlib.Topology.MetricSpace.Ultra.TotallySeparated`
- `Mathlib.Topology.Order.Compact`
- `Mathlib.Topology.Separation.Profinite`
- `Mathlib.Topology.Sequences`
- `Mathlib.Topology.UrysohnsLemma`
