# Actual extraction of two supplied special-head occurrences

Author: Worker 357.
Provenance: derived construction from published Library interfaces.

`Langlands.Classification.segmentHeadProductPairReduction` extracts any two
specified distinct occurrences from an irreducible product of supplied special
heads. It returns actual irreducible product data for those two supplied blocks,
together with an actual equivalence between the original whole product and a
permutation that puts the selected occurrences first.

The parameters are an arbitrary prime `p` with `[Fact p.Prime]`, an actual
`F : PadicField.{uF} p`, its supplied compatible topology `T`, a natural rank `n`
with `hn : 0 < n`, actual `d : T.SegmentProductDatum.{uV,uF} n`,
`hd : d.HasSegmentHeads`, irreducibility of `d.induced`, two indices
`i j : Fin d.length`, and `hij : i ≠ j`. The field universe `uF` and the
segment-base universe `uV` remain independent. The supplied block carriers and
all induced carriers here lie in `Type (max uF uV)`. The topology is always
`T.topology`; all group actions, tensor products, and inductions are the existing
actual complex representations.

Distinct indices may carry equal segments and equal representations. No
ordering, nonlinkage, twist-freeness or additive-character hypothesis is used.
The head relation is the existing strong irreducible head of increasing segment
induction from `Segments` and `LanglandsData`. It is never replaced by the segment
socle relation. The normalization is the existing upper parabolic induction with
positive half-modulus twist and right translation.

## Returned data and public helpers

`SegmentHeadProductPairReduction T d i j` stores:

| Field | Meaning |
| --- | --- |
| `length_gt_one` | There are at least two occurrence positions. |
| `permutation` | An actual permutation of the original occurrence labels. |
| `first_eq`, `second_eq` | This permutation sends positions zero and one to `i` and `j`, respectively. |
| `permutationEquiv` | An actual equivariant complex-linear equivalence from `d.induced` to the permuted whole product. |
| `datum` | Actual product data at rank `(d.segments i).degree + (d.segments j).degree`. |
| `heads` | Every block of the extracted datum satisfies the existing special-head relation. |
| `blocks_eq` | Its complete ordered block list is exactly `[d.blockAt i, d.blockAt j]`. |
| `irreducible` | The actual induced representation of the extracted datum is irreducible. |

The complete block list stores both segments and their supplied actual smooth
representations. Its equality implies length two and retains the occurrences
with their multiplicities. No new choice of segment representatives is made.
The stored permutation equivalence concerns the whole product; no equivalence
between the whole product and the extracted pair is asserted.

The same module supplies four reusable intermediate interfaces:

- `segmentHeadProductNonzeroVector T d hd` chooses an actual nonzero vector in
  any product of supplied heads. This helper allows rank zero and the empty
  family.
- `segmentHeadProductPermutationEquiv T hn d hd hirr σ` chooses an actual
  equivalence from an irreducible supplied-head product to any specified
  permutation of its factors.
- `segmentAdjacentDatum_hasSegmentHeads` restricts the supplied head proofs to
  each actual inner datum of an adjacent merge.
- `segmentAdjacentDatum_isIrreducible` proves that the merged adjacent inner
  product is irreducible when the whole product is irreducible. It takes an
  existing adjacent position and has no separate positive-total-rank premise.

## Implemented construction

For the nonzero-vector helper, the supplied head proof gives irreducibility of
every block. `IsSimpleModule.nontrivial` applied to its group-algebra module
gives a nonzero carrier. Choose a vector-space basis of every block and one
basis index for each. `Basis.piTensorProduct` gives a basis vector of the finite
external tensor, and `Basis.ne_zero` proves it is nonzero. This also handles an
empty index family. The tensor action is smooth by
`FiniteTensor.isSmooth_external`. The published
`CuspidalSupport.normalizedParabolicInduced_eval_surjective` gives a smooth
induced function with that vector as its value at the identity. A zero induced
function would have zero value there, contradicting the basis vector's
nonvanishing. The proof packages the existential preimage as `Nonempty` data
and uses `Classical.choice` to return the actual nonzero vector.

For permutation, `IsSegmentHead.isIrreducible` and
`IsSegmentHead.isAdmissible` supply the hypotheses of the published
`Parabolic.WholeLeviConjugacyProof.permutedProducts`. It gives
multiplicity-sensitive matching of finite composition factors between the
original and permuted normalized products. The elementary
`RepresentationExactComparison.nonempty_equiv_of_sameFactors` combines this
with irreducibility of the original product to give an actual equivalence.
Classical choice selects it. Thus the passage from matching factors to actual
equivalence uses the explicit whole-product irreducibility premise.

For the adjacent inner product, `d.adjacentInducedEquiv j h` regroups the whole
product into the normalized outer product on `d.shape.adjacentMerge j h`. Each
inner datum retains original block labels, so its head proofs restrict directly.
The nonzero-vector helper makes all inner carriers nonzero. Transport of the
whole-product irreducibility along the regrouping equivalence makes the outer
product irreducible. If the chosen merged inner product had a proper nonzero
invariant subspace, the published
`Parabolic.normalizedProductSlotSubrepresentation_proper_nonzero` would produce
an actual proper nonzero invariant subspace of that outer product. Its hypotheses
are discharged by the nonzero inner carriers and smoothness of the actual
induced objects. This contradicts simplicity of the outer product. Nontriviality
of the merged carrier also shows that its bottom and top subrepresentations
differ, and `IsSimpleOrder.of_forall_eq_top` concludes irreducibility.

For arbitrary selected positions, distinct finite indices imply `1 < d.length`.
Write `a = 0`, `b = 1`, `e = swap a i`, and `k = e.symm j`.
The inequality `i ≠ j` proves `k ≠ a`. The permutation
`(swap b k).trans e` therefore sends `a` to `i` and `b` to `j`.
The private helper `pairFrontPermutation` returns this actual permutation and
both equations. Apply the permutation equivalence and transport irreducibility
to the permuted whole datum. Regroup at adjacent position zero and take its
merged inner datum. The adjacent irreducibility argument applies to this datum.
`adjacentDatum_merged_blockList` and the two permutation equations identify its
complete list as `[d.blockAt i, d.blockAt j]`. The existing
`blockList_degree_sum` computes its rank as the sum of the selected segment
degrees. The private `transportHeadPair` transports the full datum, head proof,
list equality and irreducibility proof along this equality of natural ranks.
The main constructor returns those data and the whole-product permutation data.
No representation is resized or replaced during this rank transport.

## Provenance, proof dependencies and independence

This is an internal assembly of proved Library constructions and finite label,
rank and invariant-subspace arguments. It translates no new assertion from an
external source. Its purpose is a reduction step for the host special-head
criterion; the host theorem and both of its directions remain separate proof
obligations. This unit proves neither nonlinkage of the selected segments nor
the host criterion. In particular, it does not infer irreducibility merely from
nondegeneracy, constituent equality or equality in a Grothendieck group.

The six direct imports and the actual used bodies are as follows.

| Import | Used interface and inspected proof route |
| --- | --- |
| `Classification.SegmentHeadProductFiniteness` | Extracts head irreducibility from the primitive relation. Head admissibility uses the general `CuspidalSupport.cuspidalEmbedding` theorem, whose route embeds into cuspidal induction and transfers admissibility through an injection. It assumes no segment classification. |
| `Classification.SegmentProductAdjacentRefinement` | Restricts the original supplied block family to actual inner data. Its list identity is finite label bookkeeping. Its regrouping map uses `SegmentProductRefinement.refinementInducedEquiv`, then closed ordered regrouping with the exact block-coordinate identities. |
| `Parabolic.WholeLeviConjugacyProof` | Only `permutedProducts` is applied. It decomposes permutations into adjacent swaps; each swap uses normalized induction in stages, generic two-factor constituent commutativity, tensor factor matching and induction factor matching. Finite-length and admissibility inputs are general smooth-representation results. |
| `Parabolic.ProductInductionSubrepresentation` | Builds the actual finite tensor slot subspace and then the normalized induced value subspace. Nonzero complementary carriers and smoothness preserve properness and nonvanishing. |
| `Filtration.IrreducibleExactComparison` | Matching factors with a simple object force series length one. The sole successive quotient of a zero-to-whole one-slot filtration is equivalent to the original representation, giving the actual equivalence. |
| `CuspidalSupport.RefinedCuspidalInductionReduction` | Only the surjectivity of evaluation for smooth normalized induction is applied. Inflation along the continuous Levi projection and the half-modulus twist are smooth, and `Induction.compactLocalSection` supplies a section with the prescribed value. Its other conditional finite-length and Jacquet conclusions are unused. |

The generic two-factor commutativity body used by `permutedProducts` was
inspected in `Classification.TwoFactorProductConstituentCommutativityProof`.
It uses inverse transpose, smooth duality of normalized induction,
Gelfand–Kazhdan for irreducible admissible representations, finite composition
series, and annihilator-series quotient equivalences. Annihilator restriction
surjectivity follows from exactness of smooth duality and compact-open cofinality.
Pullback along the inverse-transpose automorphism detects matching factors.
There is no segment-product commutation or classification premise. The extra
whole-Levi proof branches are part of the import inventory but are not invoked
by this constructor.

The slot construction's lower bodies in `Tensor.ExternalSubrepresentation` and
`Parabolic.InductionSubrepresentation` were also inspected. The tensor proof
chooses a nonzero complementary tensor and a dual functional taking value one
on it, which reflects inclusion of the original slot subspaces. The induction
proof produces compact local sections of the restricted inducing subspace and
reflects inclusion by their values at the identity. Bottom and top are preserved,
so inclusion reflection gives nonvanishing and properness. The same smoothness
and nonzero hypotheses are present in the published product adapter and are
explicitly supplied by this module.

The head, permutation and refinement bodies retain the actual unsaturated
segment-base universe and all repeated occurrences. Definitions of socles,
essential representations, tempered representations and support appear among
inherited data interfaces, but no excluded conclusion about them is used. The
closure has no `Langlands.Representation.Derivative` or
`Langlands.Representation.Mirabolic` module. It does contain the generic group
modules `Langlands.Group.GL.Mirabolic` and
`Langlands.Group.GL.MirabolicOppositeIntersection`: the import path is
`WholeLeviConjugacyProof` → `ProductReversalFactorsProof` →
`ProductReversalFactorsStatement` → `Group.GL.MirabolicOppositeIntersection` →
`Group.GL.Mirabolic`. These provide elementary matrix-subgroup and binary-block
infrastructure, including the binary block shape used in the reversal
statement; they do not introduce derivative or mirabolic-representation theory.
The closure has no host criterion or generic segment-product uniqueness
statement, no multisegment exhaustion, ordered
strong-head existence or conversion, quotient coverage, tempered uniqueness,
square-integrable classification or exhaustion, or regular exhaustion proof.
It has no segment derivative, head/socle Jacquet formula or full Jacquet formula
input and no segment-socle part of task `8e5b4563-0365-41c7-b134-70f2a0b36292`.

The host's trusted operator decisions are recorded in correspondence files
`bd71b9185aab5d6eafffb7891bd3a3ca.md`,
`0edda6122ce65ed7ac51603c37473920.md`,
`30144f6f9b59540b88b6d4c1517892d9.md`,
`ed80148e21e7523abfc048f455e98eb0.md`,
`2b33898bdd0a5ff1b9031be5155a06f0.md`, and
`ca18fd5005bf5e12a3f7cade18dca865.md`, all under
`/home/taskhub/pilot/correspondence/`. They were read in full. This unit does not
use their derivative, support-bound, restricted intermediate-step or adjacent
reducibility permissions. All host exclusions remain in force. Neither the
replacement datum nor binary adapter nor any pending contribution is imported.
All inherited mathematics is reused by published Lean name.

## Reproducible import inventory

The recursive inventory is against published Library `ee0c0dd6da0a631f199c2bc0aa6040eece98f41d`.
It contains 732 project modules including this new root and
262 distinct external frontier imports. All
731 inherited Lean/Markdown pairs agree byte for byte with
that Library; there are no missing imports or missing Markdown pairs.
A scan of code with nested comments and string literals removed finds no proof
holes, new axioms, prohibited executable syntax or occurrence of the audited
excluded declaration/task names. The used-body audit above supplies the semantic
route; the name scan is an additional check, not a substitute for it.
No inherited file is modified by this contribution. Library-wide exact-name
search found no existing copy of these extraction constructors.

The project modules are listed in full below. External imports are listed as
they occur at the project boundary; their Mathlib and Lean dependencies are
supplied by the pinned approved environment.

### Project modules

```text
Langlands.Algebra.CommutingDimensionHelpers
Langlands.Algebra.CommutingDimensionNilpotent
Langlands.Algebra.CommutingDimensionNumerics
Langlands.Algebra.CommutingDimensionPrimary
Langlands.Algebra.CommutingDimensionRecurrence
Langlands.Algebra.SandwichDimensionBoundProof
Langlands.Algebra.SandwichDimensionBoundStatement
Langlands.Algebra.SeparatedMatrixRepresentations
Langlands.Analysis.Local.CompactOpenCoverUnimodularityProof
Langlands.Analysis.Local.CompactOpenCoverUnimodularityStatement
Langlands.Analysis.Local.ModularCompactAverage
Langlands.Analysis.Local.QuotientAutomorphismProof
Langlands.Analysis.Local.QuotientAutomorphismStatement
Langlands.Analysis.Local.QuotientAverageReal
Langlands.Analysis.Local.QuotientAveragingKernel
Langlands.Analysis.Local.QuotientComplex
Langlands.Analysis.Local.QuotientFunctional
Langlands.Analysis.Local.QuotientMass
Langlands.Analysis.Local.QuotientMeasure
Langlands.Analysis.Local.QuotientMeasureExistence
Langlands.Analysis.Local.QuotientMeasureExistenceStatement
Langlands.Analysis.Local.QuotientMeasurePrerequisites
Langlands.Analysis.Local.QuotientPositiveLifting
Langlands.Analysis.Local.QuotientTopology
Langlands.Analysis.Local.QuotientTranslation
Langlands.Analysis.Local.SplitKernelQuotient
Langlands.ClassFieldTheory.Local.Completion
Langlands.ClassFieldTheory.Local.FiniteArtin
Langlands.ClassFieldTheory.Local.Galois
Langlands.ClassFieldTheory.Local.Norms
Langlands.ClassFieldTheory.Local.ProfiniteReciprocityStatement
Langlands.ClassFieldTheory.Local.ReciprocityRelations
Langlands.ClassFieldTheory.Local.Transfer
Langlands.ClassFieldTheory.Local.Units
Langlands.ClassFieldTheory.Local.WeilAbelianization
Langlands.ClassFieldTheory.Local.WeilReciprocityStatement
Langlands.Combinatorics.RelationInversions
Langlands.Correspondence.AutomorphicRelations
Langlands.Correspondence.Domains
Langlands.Correspondence.LocalConventions
Langlands.Correspondence.OperationCompatibility
Langlands.Correspondence.SupercuspidalRelations
Langlands.Correspondence.UnramifiedNormalization
Langlands.Galois.FiniteField.Comparison
Langlands.Galois.FiniteField.ComparisonProof
Langlands.Galois.FiniteField.Frobenius
Langlands.Galois.Local.AbsoluteDefinitions
Langlands.Galois.Local.AbsoluteProof
Langlands.Galois.Local.AbsoluteStatement
Langlands.Galois.Local.SpectralDefinitions
Langlands.Galois.Local.SpectralProof
Langlands.Galois.Local.SpectralStatement
Langlands.Group.GL.AdjacentMergeShape
Langlands.Group.GL.Basic
Langlands.Group.GL.BlockContractionProof
Langlands.Group.GL.BlockContractionStatement
Langlands.Group.GL.BlockIwahoriBasis
Langlands.Group.GL.BlockIwahoriBasisStatement
Langlands.Group.GL.BlockIwahoriDefinitions
Langlands.Group.GL.BlockModulus
Langlands.Group.GL.BlockModulusHaarProof
Langlands.Group.GL.BlockModulusHaarStatement
Langlands.Group.GL.BlockUnipotentCoordinates
Langlands.Group.GL.BlockUnipotentHaarProof
Langlands.Group.GL.BlockUnipotentHaarStatement
Langlands.Group.GL.Blocks
Langlands.Group.GL.CartanProof
Langlands.Group.GL.CartanStatement
Langlands.Group.GL.CompactOpen
Langlands.Group.GL.CountabilityProof
Langlands.Group.GL.CountabilityStatement
Langlands.Group.GL.DominantExponentGeneration
Langlands.Group.GL.HeadTailBlocks
Langlands.Group.GL.IntegralSubgroup
Langlands.Group.GL.Maps
Langlands.Group.GL.Mirabolic
Langlands.Group.GL.MirabolicOppositeIntersection
Langlands.Group.GL.NestedRefinement
Langlands.Group.GL.Nonarchimedean
Langlands.Group.GL.NonarchimedeanStatement
Langlands.Group.GL.NormalizedCharacter
Langlands.Group.GL.OneBlockShape
Langlands.Group.GL.OppositeBlocks
Langlands.Group.GL.Padic
Langlands.Group.GL.PadicBlocks
Langlands.Group.GL.PadicOppositeBlocks
Langlands.Group.GL.PadicUpperUnipotent
Langlands.Group.GL.ParabolicModularCharacter
Langlands.Group.GL.PrincipalBlockFactorizationProof
Langlands.Group.GL.PrincipalBlockFactorizationStatement
Langlands.Group.GL.PrincipalLevelDominance
Langlands.Group.GL.RankMaps
Langlands.Group.GL.RefinementCoordinates
Langlands.Group.GL.ReverseBlocks
Langlands.Group.GL.SingleBlock
Langlands.Group.GL.SingletonBlocks
Langlands.Group.GL.Transvection
Langlands.Group.GL.TriangularParabolic
Langlands.Group.GL.UnramifiedCharacter
Langlands.Group.GL.UpperBruhatEmbedding
Langlands.Group.GL.UpperBruhatPivotProof
Langlands.Group.GL.UpperBruhatPivotStatement
Langlands.Group.GL.UpperBruhatProof
Langlands.Group.GL.UpperBruhatStatement
Langlands.Group.GL.UpperUnipotent
Langlands.Group.HaarModulus
Langlands.Group.LeftQuotient
Langlands.HarmonicAnalysis.AlgebraicIntegral
Langlands.HarmonicAnalysis.AlgebraicIntegrand
Langlands.HarmonicAnalysis.Basic
Langlands.HarmonicAnalysis.Conductor
Langlands.HarmonicAnalysis.Distribution.Basic
Langlands.HarmonicAnalysis.Distribution.ClosedRestrictionProof
Langlands.HarmonicAnalysis.Distribution.ClosedRestrictionStatement
Langlands.HarmonicAnalysis.Distribution.FiniteOrbitVanishingProof
Langlands.HarmonicAnalysis.Distribution.FiniteOrbitVanishingStatement
Langlands.HarmonicAnalysis.Distribution.GeneralLinear
Langlands.HarmonicAnalysis.Distribution.HomogeneousPositivityProof
Langlands.HarmonicAnalysis.Distribution.HomogeneousPositivityStatement
Langlands.HarmonicAnalysis.Distribution.HomogeneousVanishingProof
Langlands.HarmonicAnalysis.Distribution.HomogeneousVanishingStatement
Langlands.HarmonicAnalysis.Distribution.LocalizationProof
Langlands.HarmonicAnalysis.Distribution.LocalizationStatement
Langlands.HarmonicAnalysis.Distribution.Subspace
Langlands.HarmonicAnalysis.Distribution.TransposeInvariantProof
Langlands.HarmonicAnalysis.Distribution.TransposeInvariantStatement
Langlands.HarmonicAnalysis.FiniteProductMeasureScaling
Langlands.HarmonicAnalysis.HaarConjugacy
Langlands.HarmonicAnalysis.PadicHaarScalingStatement
Langlands.HarmonicAnalysis.PadicRectangularHaarScalingProof
Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof
Langlands.HarmonicAnalysis.RowTensorDecompositionProof
Langlands.HarmonicAnalysis.RowTensorDecompositionStatement
Langlands.HarmonicAnalysis.TriangularTranslationProof
Langlands.HarmonicAnalysis.TriangularTranslationStatement
Langlands.LinearAlgebra.CyclicQuotientPairingProof
Langlands.LinearAlgebra.CyclicQuotientPairingStatement
Langlands.LinearAlgebra.FiniteRankTrace
Langlands.LinearAlgebra.FiniteRankTranspose
Langlands.LinearAlgebra.MatrixAEvalConjugacyProof
Langlands.LinearAlgebra.MatrixAEvalConjugacyStatement
Langlands.LinearAlgebra.MatrixCharpolyConjugacyProof
Langlands.LinearAlgebra.MatrixCharpolyConjugacyStatement
Langlands.LinearAlgebra.MatrixTransposeConjugateProof
Langlands.LinearAlgebra.MatrixTransposeConjugateStatement
Langlands.LinearAlgebra.PolynomialModuleBoundedCyclicDecompositionProof
Langlands.LinearAlgebra.PolynomialModuleBoundedCyclicDecompositionStatement
Langlands.LocalFactor.RankOne
Langlands.LocalField.Canonical
Langlands.LocalField.CanonicalProof
Langlands.LocalField.CanonicalStatement
Langlands.LocalField.Definitions
Langlands.LocalField.Normalization.Definitions
Langlands.LocalField.Normalization.Proof
Langlands.LocalField.Normalization.Statement
Langlands.LocalField.Topology
Langlands.LocalField.Uniformizer
Langlands.Representation.Category.Basic
Langlands.Representation.Category.ClassInvariants
Langlands.Representation.Category.Contragredient
Langlands.Representation.Category.Subquotients
Langlands.Representation.Category.Twist
Langlands.Representation.Character.Basic
Langlands.Representation.Character.SeparationProof
Langlands.Representation.Character.SeparationStatement
Langlands.Representation.Character.TransportProof
Langlands.Representation.Character.TransportStatement
Langlands.Representation.Classification.ConstituentRelations
Langlands.Representation.Classification.CuspidalIntegralTwistFreenessStatement
Langlands.Representation.Classification.Essential
Langlands.Representation.Classification.FiniteLengthProof
Langlands.Representation.Classification.FiniteLengthStatement
Langlands.Representation.Classification.IrreducibleProductEmbedding
Langlands.Representation.Classification.IrreducibleProductEmbeddingStatement
Langlands.Representation.Classification.IrreducibleProductFiniteLengthProof
Langlands.Representation.Classification.LanglandsData
Langlands.Representation.Classification.NormalizedProductFiniteLengthProof
Langlands.Representation.Classification.NormalizedProductFiniteLengthStatement
Langlands.Representation.Classification.SegmentHeadProductFiniteness
Langlands.Representation.Classification.SegmentHeadProductPairReduction
Langlands.Representation.Classification.SegmentIntegralCoordinates
Langlands.Representation.Classification.SegmentIntervalLinkage
Langlands.Representation.Classification.SegmentProductAdjacentRefinement
Langlands.Representation.Classification.SegmentProductAdjacentReplacement
Langlands.Representation.Classification.SegmentProductPermutation
Langlands.Representation.Classification.SegmentProductRefinement
Langlands.Representation.Classification.SegmentProductReplacement
Langlands.Representation.Classification.SegmentReplacementInversions
Langlands.Representation.Classification.SegmentUnionIntersection
Langlands.Representation.Classification.Segments
Langlands.Representation.Classification.Supercuspidal
Langlands.Representation.Classification.SupercuspidalContragredientAux
Langlands.Representation.Classification.SupercuspidalContragredientStatement
Langlands.Representation.Classification.SupercuspidalSupport
Langlands.Representation.Classification.SupercuspidalTwist
Langlands.Representation.Classification.Tempered
Langlands.Representation.Classification.TwoFactorProductConstituentCommutativityProof
Langlands.Representation.Classification.TwoFactorProductConstituentCommutativityStatement
Langlands.Representation.Compact.Definitions
Langlands.Representation.Compact.FiniteMean
Langlands.Representation.Compact.OrbitMeanTranslation
Langlands.Representation.Compact.ProjectionProof
Langlands.Representation.Compact.ProjectionStatement
Langlands.Representation.Compact.SurjectivityProof
Langlands.Representation.Compact.SurjectivityStatement
Langlands.Representation.CompactCoefficient.AdmissibleComplement
Langlands.Representation.CompactCoefficient.AdmissibleLifting
Langlands.Representation.CompactCoefficient.AdmissibleRetraction
Langlands.Representation.CompactCoefficient.AmbientProjector
Langlands.Representation.CompactCoefficient.Classes
Langlands.Representation.CompactCoefficient.ConditionalProjection
Langlands.Representation.CompactCoefficient.FixedLevelFiniteness
Langlands.Representation.CompactCoefficient.FixedVectorsFiniteDimensional
Langlands.Representation.CompactCoefficient.GroupTransport
Langlands.Representation.CompactCoefficient.Isotypic
Langlands.Representation.CompactCoefficient.IsotypicTransport
Langlands.Representation.CompactCoefficient.NormalSubgroupDecomposition
Langlands.Representation.CompactCoefficient.OrthogonalProjectorFamily
Langlands.Representation.CompactCoefficient.SemisimplicityProof
Langlands.Representation.CompactCoefficient.SemisimplicityStatement
Langlands.Representation.CompactCoefficient.TotalCompactness
Langlands.Representation.CompactCoefficient.TotalProjector
Langlands.Representation.Conductor.Congruence
Langlands.Representation.Conductor.Definitions
Langlands.Representation.Conductor.PrincipalCongruence
Langlands.Representation.Conductor.PrincipalCongruenceBasisProof
Langlands.Representation.Conductor.PrincipalCongruenceBasisStatement
Langlands.Representation.CuspidalSupport.AdjacentMergedTensor
Langlands.Representation.CuspidalSupport.AssociatedAssembly
Langlands.Representation.CuspidalSupport.AssociatedConditional
Langlands.Representation.CuspidalSupport.AssociatedGeometricPieceVanishingProof
Langlands.Representation.CuspidalSupport.AssociatedGeometricPiecesEquivalenceProof
Langlands.Representation.CuspidalSupport.AssociatedGeometricPiecesProof
Langlands.Representation.CuspidalSupport.AssociatedGeometricPiecesStatement
Langlands.Representation.CuspidalSupport.AssociatedProof
Langlands.Representation.CuspidalSupport.AssociatedRankZero
Langlands.Representation.CuspidalSupport.AssociationForwardStatement
Langlands.Representation.CuspidalSupport.AssociationLawsProof
Langlands.Representation.CuspidalSupport.AssociationLawsStatement
Langlands.Representation.CuspidalSupport.AssociationReduction
Langlands.Representation.CuspidalSupport.BlockMap
Langlands.Representation.CuspidalSupport.BlockPermutation
Langlands.Representation.CuspidalSupport.BlockPermutationTensor
Langlands.Representation.CuspidalSupport.CompactCoefficientFinitenessProof
Langlands.Representation.CuspidalSupport.CompactCoefficientFinitenessReduction
Langlands.Representation.CuspidalSupport.CompactCoefficientFinitenessStatement
Langlands.Representation.CuspidalSupport.CuspidalEmbeddingProof
Langlands.Representation.CuspidalSupport.CuspidalTensorAssociationProof
Langlands.Representation.CuspidalSupport.CuspidalTensorProof
Langlands.Representation.CuspidalSupport.CuspidalTensorStatement
Langlands.Representation.CuspidalSupport.CuspidalityComparisonProof
Langlands.Representation.CuspidalSupport.CuspidalityComparisonStatement
Langlands.Representation.CuspidalSupport.DeterminantUnit
Langlands.Representation.CuspidalSupport.DeterminantUnitCartanSupport
Langlands.Representation.CuspidalSupport.DeterminantUnitCentralCompactnessProof
Langlands.Representation.CuspidalSupport.DeterminantUnitCentralCompactnessStatement
Langlands.Representation.CuspidalSupport.DeterminantUnitCornerStructureProof
Langlands.Representation.CuspidalSupport.DeterminantUnitCornerStructureStatement
Langlands.Representation.CuspidalSupport.DeterminantUnitStructureProof
Langlands.Representation.CuspidalSupport.DeterminantUnitStructureStatement
Langlands.Representation.CuspidalSupport.DualAveraging
Langlands.Representation.CuspidalSupport.FiltrationQuasicuspidality
Langlands.Representation.CuspidalSupport.FiniteBlockShapes
Langlands.Representation.CuspidalSupport.GroupTransport
Langlands.Representation.CuspidalSupport.HarishChandraAssembly
Langlands.Representation.CuspidalSupport.HarishChandraBoundaryProof
Langlands.Representation.CuspidalSupport.HarishChandraBoundaryStatement
Langlands.Representation.CuspidalSupport.HarishChandraConverseProof
Langlands.Representation.CuspidalSupport.HarishChandraConverseStatement
Langlands.Representation.CuspidalSupport.HarishChandraForwardProof
Langlands.Representation.CuspidalSupport.HarishChandraStatement
Langlands.Representation.CuspidalSupport.InducedJacquetCount
Langlands.Representation.CuspidalSupport.InducedJacquetEvaluation
Langlands.Representation.CuspidalSupport.IrreducibleLeviAdmissibilityProof
Langlands.Representation.CuspidalSupport.IrreducibleLeviAdmissibilityStatement
Langlands.Representation.CuspidalSupport.JacquetDetectingFamilyLengthProof
Langlands.Representation.CuspidalSupport.JacquetDetectingFamilyLengthStatement
Langlands.Representation.CuspidalSupport.JacquetInductionStatement
Langlands.Representation.CuspidalSupport.JacquetLengthDetector
Langlands.Representation.CuspidalSupport.JacquetSubquotientProof
Langlands.Representation.CuspidalSupport.JacquetSubquotientStatement
Langlands.Representation.CuspidalSupport.JacquetVanishingHelpers
Langlands.Representation.CuspidalSupport.JacquetVanishingSmoothPieces
Langlands.Representation.CuspidalSupport.JacquetVanishingSubgroups
Langlands.Representation.CuspidalSupport.LeviAdmissibleFactorizationProof
Langlands.Representation.CuspidalSupport.LeviAdmissibleFactorizationStatement
Langlands.Representation.CuspidalSupport.LeviAssociation
Langlands.Representation.CuspidalSupport.LeviCompactPart
Langlands.Representation.CuspidalSupport.LeviDecompositionAssembly
Langlands.Representation.CuspidalSupport.LeviDefinitions
Langlands.Representation.CuspidalSupport.LeviGapVanishing
Langlands.Representation.CuspidalSupport.LeviQuasicuspidalDecompositionProof
Langlands.Representation.CuspidalSupport.LeviSplitContraction
Langlands.Representation.CuspidalSupport.LeviTensorFactorizationProof
Langlands.Representation.CuspidalSupport.LeviTensorFactorizationStatement
Langlands.Representation.CuspidalSupport.LeviTensorReflectionProof
Langlands.Representation.CuspidalSupport.LeviTensorReflectionStatement
Langlands.Representation.CuspidalSupport.MinimalConjugatingCosetsProof
Langlands.Representation.CuspidalSupport.MinimalJacquetProof
Langlands.Representation.CuspidalSupport.MinimalJacquetStatement
Langlands.Representation.CuspidalSupport.MinimalRefinedJacquetProof
Langlands.Representation.CuspidalSupport.MinimalRefinedJacquetStatement
Langlands.Representation.CuspidalSupport.MinimalWeylTransportProof
Langlands.Representation.CuspidalSupport.NaturalProjectorDecomposition
Langlands.Representation.CuspidalSupport.NonassociatedJacquetSubquotientsProof
Langlands.Representation.CuspidalSupport.NormalizedCuspidalInductionLengthProof
Langlands.Representation.CuspidalSupport.NormalizedCuspidalInductionStatement
Langlands.Representation.CuspidalSupport.PointwiseProjectorSum
Langlands.Representation.CuspidalSupport.ProperInductionMaps
Langlands.Representation.CuspidalSupport.ProperInductionProof
Langlands.Representation.CuspidalSupport.ProperInductionStatement
Langlands.Representation.CuspidalSupport.QuasicuspidalEmbeddingProof
Langlands.Representation.CuspidalSupport.QuasicuspidalFiniteLengthProof
Langlands.Representation.CuspidalSupport.QuasicuspidalFiniteLengthStatement
Langlands.Representation.CuspidalSupport.QuasicuspidalLeviAdmissibilityProof
Langlands.Representation.CuspidalSupport.QuasicuspidalPrerequisitesStatement
Langlands.Representation.CuspidalSupport.QuasicuspidalStructureStatement
Langlands.Representation.CuspidalSupport.RefinedCuspidalInductionLengthStatement
Langlands.Representation.CuspidalSupport.RefinedCuspidalInductionRankZero
Langlands.Representation.CuspidalSupport.RefinedCuspidalInductionReduction
Langlands.Representation.CuspidalSupport.RefinedJacquetLengthProof
Langlands.Representation.CuspidalSupport.RefinedJacquetLengthStatement
Langlands.Representation.CuspidalSupport.RefinedQuasicuspidalEmbeddingProof
Langlands.Representation.CuspidalSupport.RefinedQuasicuspidalEmbeddingStatement
Langlands.Representation.CuspidalSupport.StandardJacquetComparisonProof
Langlands.Representation.CuspidalSupport.TotalConjugatingCountProof
Langlands.Representation.CuspidalSupport.TotalConjugatingCountStatement
Langlands.Representation.CuspidalSupport.ZeroRankEmbeddingProof
Langlands.Representation.Dual.Definitions
Langlands.Representation.Exponents.ParabolicPair
Langlands.Representation.Filtration.CoinvariantVanishingStatement
Langlands.Representation.Filtration.Definitions
Langlands.Representation.Filtration.FactorMatchingPullback
Langlands.Representation.Filtration.GradedRefinementProof
Langlands.Representation.Filtration.GradedRefinementStatement
Langlands.Representation.Filtration.IntervalLiftProof
Langlands.Representation.Filtration.IntervalLiftStatement
Langlands.Representation.Filtration.IrreducibleEmbedding
Langlands.Representation.Filtration.IrreducibleExactComparison
Langlands.Representation.Filtration.IrreducibleMultiplicityProof
Langlands.Representation.Filtration.IrreducibleMultiplicityStatement
Langlands.Representation.Filtration.IsoTransport
Langlands.Representation.Filtration.JordanHolderComparisonProof
Langlands.Representation.Filtration.JordanHolderProof
Langlands.Representation.Filtration.JordanHolderStatement
Langlands.Representation.Filtration.JordanHolderTransportProof
Langlands.Representation.Filtration.LengthCriterionProof
Langlands.Representation.Filtration.LengthCriterionStatement
Langlands.Representation.Filtration.LengthTwoMatching
Langlands.Representation.Filtration.LengthTwoMatchingStatement
Langlands.Representation.Filtration.MultiplicityAdditivityProof
Langlands.Representation.Filtration.MultiplicityAdditivityStatement
Langlands.Representation.Filtration.MultiplicityIndependenceProof
Langlands.Representation.Filtration.MultiplicityStatement
Langlands.Representation.Filtration.MultiplicityTransportProof
Langlands.Representation.Filtration.MultiplicityTransportStatement
Langlands.Representation.Filtration.ObjectDefinitions
Langlands.Representation.Filtration.ObjectTransport
Langlands.Representation.Filtration.QuasicuspidalVanishingProof
Langlands.Representation.Filtration.QuotientFirstIso
Langlands.Representation.Filtration.RepresentationLength
Langlands.Representation.Filtration.SubsingletonProof
Langlands.Representation.Filtration.Transport
Langlands.Representation.Filtration.VanishingStatement
Langlands.Representation.Filtration.ZeroFactorDeletionProof
Langlands.Representation.Filtration.ZeroFactorDeletionStatement
Langlands.Representation.Geometric.BlockIntersectionSplitting
Langlands.Representation.Geometric.BlockSixDecomposableProof
Langlands.Representation.Geometric.BlockSixDecomposableStatement
Langlands.Representation.Geometric.BruhatDescent
Langlands.Representation.Geometric.BruhatMatrixExistenceProof
Langlands.Representation.Geometric.BruhatMatrixStatement
Langlands.Representation.Geometric.BruhatWeylReflectionProof
Langlands.Representation.Geometric.ClosedSubgroupAssembly
Langlands.Representation.Geometric.ClosedSubgroupDefinitions
Langlands.Representation.Geometric.ClosedSubgroupMackeyProof
Langlands.Representation.Geometric.ClosedSubgroupStatement
Langlands.Representation.Geometric.CompactOrbitRestriction
Langlands.Representation.Geometric.CompactSmoothComparison
Langlands.Representation.Geometric.ConditionalAssembly
Langlands.Representation.Geometric.CorrectionSubgroupCoordinates
Langlands.Representation.Geometric.CorrectionSubgroupDiagonalHaarProof
Langlands.Representation.Geometric.CorrectionSubgroupDiagonalHaarStatement
Langlands.Representation.Geometric.CosetAction
Langlands.Representation.Geometric.CosetOrbitHomeomorph
Langlands.Representation.Geometric.CosetOrbitOrdering
Langlands.Representation.Geometric.FlattenedLevi
Langlands.Representation.Geometric.GeneralCorrectionCharacters
Langlands.Representation.Geometric.GeneralIntersectionNormalizers
Langlands.Representation.Geometric.GeneralIntersections
Langlands.Representation.Geometric.GeometricLemmaProof
Langlands.Representation.Geometric.GeometricLemmaStatement
Langlands.Representation.Geometric.IntersectionLeviDiagonalCharacterProof
Langlands.Representation.Geometric.IntersectionLeviDiagonalCharacterStatement
Langlands.Representation.Geometric.IntersectionLeviModulusBalance
Langlands.Representation.Geometric.IntersectionTransport
Langlands.Representation.Geometric.MonotoneBlocksProof
Langlands.Representation.Geometric.MonotoneBlocksStatement
Langlands.Representation.Geometric.OrbitRepresentatives
Langlands.Representation.Geometric.OrbitRestriction
Langlands.Representation.Geometric.OrbitSectionExtensionProof
Langlands.Representation.Geometric.OrbitSectionExtensionStatement
Langlands.Representation.Geometric.PadicCorrectionCancellationProof
Langlands.Representation.Geometric.PadicCorrectionCancellationStatement
Langlands.Representation.Geometric.PadicParabolicBruhatProof
Langlands.Representation.Geometric.ParabolicOrbitCoefficientComparison
Langlands.Representation.Geometric.ParabolicOrbitCompactComparison
Langlands.Representation.Geometric.ParabolicOrbitComparisonData
Langlands.Representation.Geometric.ParabolicOrbitHaarComparison
Langlands.Representation.Geometric.ParabolicOrbitHaarRatio
Langlands.Representation.Geometric.ParabolicOrbitHaarTransport
Langlands.Representation.Geometric.ParabolicOrbitInductionTransport
Langlands.Representation.Geometric.ParabolicOrbitJacquet
Langlands.Representation.Geometric.ParabolicOrbitJacquetProof
Langlands.Representation.Geometric.ParabolicOrbitJacquetStatement
Langlands.Representation.Geometric.ParabolicOrbitMeasureData
Langlands.Representation.Geometric.ParabolicOrbitNestedAction
Langlands.Representation.Geometric.ParabolicOrbitNormalization
Langlands.Representation.Geometric.ParabolicOrbitNormalizedCoefficient
Langlands.Representation.Geometric.ParabolicOrbitSectionComparison
Langlands.Representation.Geometric.ParabolicOrbitStagesCoefficient
Langlands.Representation.Geometric.ParabolicSupportFiltration
Langlands.Representation.Geometric.ParabolicSupportGradedProof
Langlands.Representation.Geometric.ParabolicSupportGradedStatement
Langlands.Representation.Geometric.ParabolicSupportJacquetProof
Langlands.Representation.Geometric.ParabolicSupportJacquetStatement
Langlands.Representation.Geometric.ParabolicSupportTransport
Langlands.Representation.Geometric.RefinedPositiveCharacter
Langlands.Representation.Geometric.RefinementDefinitions
Langlands.Representation.Geometric.RefinementFunctors
Langlands.Representation.Geometric.RefinementUniqueness
Langlands.Representation.Geometric.SmoothSupportFiltration
Langlands.Representation.Geometric.StandardIntersectionsProof
Langlands.Representation.Geometric.WeylDefinitions
Langlands.Representation.Geometric.WeylMinimalRepresentativeProof
Langlands.Representation.Geometric.WeylStatement
Langlands.Representation.Geometric.WeylUniquenessProof
Langlands.Representation.Geometric.WeylUniquenessStatement
Langlands.Representation.Hecke.ActionIntegrand
Langlands.Representation.Hecke.ActionProjection
Langlands.Representation.Hecke.CommonInvarianceProof
Langlands.Representation.Hecke.CommonInvarianceStatement
Langlands.Representation.Hecke.Convolution
Langlands.Representation.Hecke.Corner
Langlands.Representation.Hecke.CornerAction
Langlands.Representation.Hecke.CornerDetermination
Langlands.Representation.Hecke.DoubleCoset
Langlands.Representation.Hecke.DoubleCosetSandwich
Langlands.Representation.Hecke.FiniteRankAction
Langlands.Representation.Hecke.IntegratedAction
Langlands.Representation.Hecke.IntegratedConvolution
Langlands.Representation.Hecke.NormalizedIndicator
Langlands.Representation.Hecke.SmoothTranspose
Langlands.Representation.Hecke.TestFunction
Langlands.Representation.Induction.BlockEquivalence
Langlands.Representation.Induction.BlockFactors
Langlands.Representation.Induction.CharacterTwistProof
Langlands.Representation.Induction.CompactAutomorphism
Langlands.Representation.Induction.CompactAutomorphismIntegralProof
Langlands.Representation.Induction.CompactAutomorphismIntegralStatement
Langlands.Representation.Induction.CompactBilinearPairing
Langlands.Representation.Induction.CompactCoinvariantBijectivityProof
Langlands.Representation.Induction.CompactCoinvariantBijectivityStatement
Langlands.Representation.Induction.CompactCoinvariantIntegral
Langlands.Representation.Induction.CompactCoinvariantLocalInverseProof
Langlands.Representation.Induction.CompactCoinvariantLocalInverseStatement
Langlands.Representation.Induction.CompactLocalSection
Langlands.Representation.Induction.CompactLocalSectionSpanningProof
Langlands.Representation.Induction.CompactLocalSectionSpanningStatement
Langlands.Representation.Induction.CompactLocallyConstant
Langlands.Representation.Induction.CompactPairingDuality
Langlands.Representation.Induction.CompactQuotientCutoff
Langlands.Representation.Induction.CompactQuotientProof
Langlands.Representation.Induction.CompactScalarProof
Langlands.Representation.Induction.CompactScalarStatement
Langlands.Representation.Induction.CompactSurjectivityProof
Langlands.Representation.Induction.CompactSurjectivityStatement
Langlands.Representation.Induction.CompactTransitivityProof
Langlands.Representation.Induction.CompactTransitivityStatement
Langlands.Representation.Induction.ConjugateParabolic
Langlands.Representation.Induction.Definitions
Langlands.Representation.Induction.Equivalences
Langlands.Representation.Induction.FiniteProductTensor
Langlands.Representation.Induction.FiniteProductTensorBijectiveProof
Langlands.Representation.Induction.FiniteProductTensorBijectiveStatement
Langlands.Representation.Induction.InverseTranspose
Langlands.Representation.Induction.NormalCoinvariantKernelProof
Langlands.Representation.Induction.NormalCoinvariantKernelStatement
Langlands.Representation.Induction.NormalCoinvariantMap
Langlands.Representation.Induction.NormalCoinvariantProof
Langlands.Representation.Induction.NormalCoinvariantStatement
Langlands.Representation.Induction.NormalSplitComparison
Langlands.Representation.Induction.OppositeParabolic
Langlands.Representation.Induction.OppositeProductReversalProof
Langlands.Representation.Induction.OppositeProductReversalStatement
Langlands.Representation.Induction.Parabolic
Langlands.Representation.Induction.PiScalarIntegral
Langlands.Representation.Induction.SingleBlock
Langlands.Representation.Induction.SplitKernelCompact
Langlands.Representation.Induction.SplitKernelCovariance
Langlands.Representation.Induction.SplitKernelEquivariant
Langlands.Representation.Induction.SplitKernelIntegral
Langlands.Representation.Induction.SplitQuotientProof
Langlands.Representation.Induction.SplitQuotientStatement
Langlands.Representation.Induction.SplitStagesComparison
Langlands.Representation.Induction.SplitStagesRetraction
Langlands.Representation.Induction.StructuralStatement
Langlands.Representation.Induction.SurjectivityProof
Langlands.Representation.Induction.SurjectivityStatement
Langlands.Representation.Jacquet.BlockCompressionProof
Langlands.Representation.Jacquet.BlockCompressionStatement
Langlands.Representation.Jacquet.BlockPowerKernelProof
Langlands.Representation.Jacquet.CanonicalLiftBijectivityProof
Langlands.Representation.Jacquet.CanonicalLiftDefinitions
Langlands.Representation.Jacquet.CanonicalLiftStatement
Langlands.Representation.Jacquet.CharacterTwistEquiv
Langlands.Representation.Jacquet.Coinvariants
Langlands.Representation.Jacquet.CompressionStabilizationProof
Langlands.Representation.Jacquet.CompressionStabilizationStatement
Langlands.Representation.Jacquet.ExactProof
Langlands.Representation.Jacquet.ExactStatement
Langlands.Representation.Jacquet.Normalized
Langlands.Representation.Jacquet.Parabolic
Langlands.Representation.Jacquet.PositiveCharacter
Langlands.Representation.Jacquet.SmoothTwist
Langlands.Representation.MatrixCoefficient.Definitions
Langlands.Representation.MatrixCoefficient.LawsProof
Langlands.Representation.MatrixCoefficient.LawsStatement
Langlands.Representation.MatrixCoefficient.ModuloCenter
Langlands.Representation.OrbitSpan
Langlands.Representation.Parabolic.AdmissibilityStatement
Langlands.Representation.Parabolic.ComposedFlattenedInductionProof
Langlands.Representation.Parabolic.ComposedFlattenedInductionStatement
Langlands.Representation.Parabolic.ComposedFunctors
Langlands.Representation.Parabolic.ExactnessReciprocityStatement
Langlands.Representation.Parabolic.FiniteLengthFunctorProof
Langlands.Representation.Parabolic.FiniteLengthFunctorStatement
Langlands.Representation.Parabolic.FlattenedJacquetQuotientProof
Langlands.Representation.Parabolic.FlattenedJacquetQuotientStatement
Langlands.Representation.Parabolic.FlattenedRefinementModulusCalculation
Langlands.Representation.Parabolic.GeometricPrerequisitesStatement
Langlands.Representation.Parabolic.InductionExactnessProof
Langlands.Representation.Parabolic.InductionFactorMatchingProof
Langlands.Representation.Parabolic.InductionFactorMatchingStatement
Langlands.Representation.Parabolic.InductionFiltration
Langlands.Representation.Parabolic.InductionSubrepresentation
Langlands.Representation.Parabolic.InverseTransposeProductProof
Langlands.Representation.Parabolic.InverseTransposeProductStatement
Langlands.Representation.Parabolic.JacquetFiniteGenerationProof
Langlands.Representation.Parabolic.JacquetFiniteGenerationStatement
Langlands.Representation.Parabolic.LeviBridges
Langlands.Representation.Parabolic.LeviInflationAdmissibilityProof
Langlands.Representation.Parabolic.NaturalFirstAdjointness
Langlands.Representation.Parabolic.NaturalInductionDualityFromScalar
Langlands.Representation.Parabolic.NaturalInductionDualityProof
Langlands.Representation.Parabolic.NaturalInductionDualityStatement
Langlands.Representation.Parabolic.NormalizedAdmissibilityProof
Langlands.Representation.Parabolic.NormalizedInductionStatement
Langlands.Representation.Parabolic.NormalizedJacquetAdmissibilityProof
Langlands.Representation.Parabolic.NormalizedJacquetExactnessProof
Langlands.Representation.Parabolic.NormalizedJacquetStatement
Langlands.Representation.Parabolic.OrderedProductRegroupingEquivalence
Langlands.Representation.Parabolic.OrderedProductRegroupingProof
Langlands.Representation.Parabolic.OrderedProductRegroupingStatement
Langlands.Representation.Parabolic.OrderedRefinementInduction
Langlands.Representation.Parabolic.OrderedRefinementTensorInduction
Langlands.Representation.Parabolic.ProductInductionSubrepresentation
Langlands.Representation.Parabolic.ProductReversalFactorsProof
Langlands.Representation.Parabolic.ProductReversalFactorsStatement
Langlands.Representation.Parabolic.QuotientCompactProof
Langlands.Representation.Parabolic.RefinedInductionAdmissibility
Langlands.Representation.Parabolic.RefinedInductionTensorMap
Langlands.Representation.Parabolic.RefinedInductionTensorNormalization
Langlands.Representation.Parabolic.RefinedInductionTensorProof
Langlands.Representation.Parabolic.RefinedInductionTensorStatement
Langlands.Representation.Parabolic.RefinedInnerInductionObjects
Langlands.Representation.Parabolic.RefinementCharacter
Langlands.Representation.Parabolic.RefinementComposition
Langlands.Representation.Parabolic.RefinementCoordinatesNormalizationProof
Langlands.Representation.Parabolic.RefinementCoordinatesNormalizationStatement
Langlands.Representation.Parabolic.RefinementInductionTransitivityProof
Langlands.Representation.Parabolic.RefinementPreimage
Langlands.Representation.Parabolic.RefinementTransitivityStatement
Langlands.Representation.Parabolic.UnipotentFiniteContainment
Langlands.Representation.Parabolic.WholeLeviConjugacyProof
Langlands.Representation.Parabolic.WholeLeviConjugacyStatement
Langlands.Representation.RankinSelberg.GeneralLinearUnimodularity
Langlands.Representation.RankinSelberg.HaarSymmetriesProof
Langlands.Representation.RankinSelberg.HaarSymmetriesStatement
Langlands.Representation.RankinSelberg.Measures
Langlands.Representation.RankinSelberg.UnimodularityStatement
Langlands.Representation.RankinSelberg.UnipotentUnimodularity
Langlands.Representation.Schur.CountableDimensionProof
Langlands.Representation.Schur.CountableDimensionStatement
Langlands.Representation.Smooth.Admissibility.CofinalProof
Langlands.Representation.Smooth.Admissibility.CofinalStatement
Langlands.Representation.Smooth.Admissibility.EmbeddingProof
Langlands.Representation.Smooth.Admissibility.EmbeddingStatement
Langlands.Representation.Smooth.Admissibility.EquivalenceProof
Langlands.Representation.Smooth.Admissibility.EquivalenceStatement
Langlands.Representation.Smooth.Admissibility.ExactProof
Langlands.Representation.Smooth.Admissibility.ExactStatement
Langlands.Representation.Smooth.Admissibility.FiniteLengthProof
Langlands.Representation.Smooth.Admissibility.FiniteLengthStatement
Langlands.Representation.Smooth.Contragredient.AdmissibleDualityProof
Langlands.Representation.Smooth.Contragredient.AdmissibleDualityStatement
Langlands.Representation.Smooth.Contragredient.CompactDualityProof
Langlands.Representation.Smooth.Contragredient.CompactDualityStatement
Langlands.Representation.Smooth.Contragredient.Definitions
Langlands.Representation.Smooth.Contragredient.ExactProof
Langlands.Representation.Smooth.Contragredient.ExactStatement
Langlands.Representation.Smooth.Contragredient.FixedVectorsDefinitions
Langlands.Representation.Smooth.Contragredient.GelfandKazhdanAssembly
Langlands.Representation.Smooth.Contragredient.GelfandKazhdanProof
Langlands.Representation.Smooth.Contragredient.GelfandKazhdanStatement
Langlands.Representation.Smooth.Contragredient.HomDualityProof
Langlands.Representation.Smooth.Contragredient.HomDualityStatement
Langlands.Representation.Smooth.Contragredient.InvariantPairingProof
Langlands.Representation.Smooth.Contragredient.InvariantPairingStatement
Langlands.Representation.Smooth.Contragredient.LawsProof
Langlands.Representation.Smooth.Contragredient.LawsStatement
Langlands.Representation.Smooth.Definitions
Langlands.Representation.Smooth.Factorization.MultiplicityDefinitions
Langlands.Representation.Smooth.Factorization.TwoFactorExistenceProof
Langlands.Representation.Smooth.Factorization.TwoFactorStatement
Langlands.Representation.Smooth.FiniteLengthGrothendieck
Langlands.Representation.Smooth.FiniteLengthGrothendieckFunctor
Langlands.Representation.Smooth.FixedVectors.Definitions
Langlands.Representation.Smooth.FixedVectors.FiniteTypes
Langlands.Representation.Smooth.FixedVectors.FiniteTypesStatement
Langlands.Representation.Smooth.FixedVectors.LawsProof
Langlands.Representation.Smooth.FixedVectors.LawsStatement
Langlands.Representation.Smooth.FixedVectors.OrderProof
Langlands.Representation.Smooth.FixedVectors.OrderStatement
Langlands.Representation.Smooth.IrreducibleRealization
Langlands.Representation.Smooth.Schur.Proof
Langlands.Representation.Smooth.Schur.Statement
Langlands.Representation.Smooth.SmallRealizationProof
Langlands.Representation.Smooth.SmallRealizationStatement
Langlands.Representation.Smooth.SmoothPart.BasicProof
Langlands.Representation.Smooth.SmoothPart.BasicStatement
Langlands.Representation.Smooth.SmoothPart.Definitions
Langlands.Representation.Smooth.SmoothPart.FixedVectorsDefinitions
Langlands.Representation.Smooth.Transfer.GroupEquivalence
Langlands.Representation.Smooth.Transfer.PullbackProof
Langlands.Representation.Smooth.Transfer.PullbackStatement
Langlands.Representation.Smooth.Transfer.SubquotientProof
Langlands.Representation.Smooth.Transfer.SubquotientStatement
Langlands.Representation.SubrepresentationLattice
Langlands.Representation.Tensor.CoinvariantReflection
Langlands.Representation.Tensor.ExternalFiltration
Langlands.Representation.Tensor.ExternalSubrepresentation
Langlands.Representation.Tensor.FactorMatchingProof
Langlands.Representation.Tensor.FactorMatchingStatement
Langlands.Representation.Tensor.Filtration
Langlands.Representation.Tensor.Finite
Langlands.Representation.Tensor.FiniteEquivalences
Langlands.Representation.Tensor.FiniteFiltration
Langlands.Representation.Tensor.FiniteProperties
Langlands.Representation.Tensor.FiniteRegrouping
Langlands.Representation.Tensor.GLRefinement
Langlands.Representation.Tensor.ProductFiltration
Langlands.Representation.Tensor.SmoothDual
Langlands.Representation.Tensor.SmoothDualInjectivityProof
Langlands.Representation.Tensor.SmoothDualInjectivityStatement
Langlands.Representation.Tensor.SmoothDualSurjectivityProof
Langlands.Representation.Tensor.SmoothDualSurjectivityStatement
Langlands.Representation.Twist.AdmissibilityProof
Langlands.Representation.Twist.AdmissibilityStatement
Langlands.Representation.Twist.AlgebraProof
Langlands.Representation.Twist.AlgebraStatement
Langlands.Representation.Twist.ContinuousCharacterProof
Langlands.Representation.Twist.ContinuousCharacterStatement
Langlands.Representation.Twist.Definitions
Langlands.Representation.Twist.DualProof
Langlands.Representation.Twist.DualStatement
Langlands.Representation.Twist.PullbackProof
Langlands.Representation.Twist.PullbackStatement
Langlands.Representation.Twist.RealPower
Langlands.Representation.Twist.SmoothPartDefinitions
Langlands.Representation.Twist.SmoothProof
Langlands.Representation.Twist.SmoothStatement
Langlands.Representation.Twist.SubquotientDefinitions
Langlands.Representation.Twist.SubquotientProof
Langlands.Representation.Twist.SubquotientStatement
Langlands.Representation.Unitary.Basic
Langlands.Representation.Unramified.Eigenvalues
Langlands.Representation.Unramified.HeckeOperators
Langlands.Representation.Unramified.PrincipalSeries
Langlands.Representation.Unramified.SphericalClassificationStatement
Langlands.Representation.Unramified.SphericalConstituentExistenceProof
Langlands.Representation.Whittaker.Iwasawa
Langlands.Topology.CompactNormCharacter
Langlands.Topology.CompactOpen.ConjugationStabilizer
Langlands.Topology.CompactOpen.NeighborhoodBasis
Langlands.Topology.CompactOpen.NeighborhoodBasisStatement
Langlands.Topology.GroupAction.FiniteOrbitProof
Langlands.Topology.GroupAction.FiniteOrbitStatement
Langlands.Topology.Nonarchimedean.Subgroup
Langlands.VirtualRepresentation.Exact
Langlands.VirtualRepresentation.ExactTwist
Langlands.VirtualRepresentation.Integral
Langlands.Weil.Algebraic
Langlands.Weil.AlgebraicProof
Langlands.Weil.Local.Assembly
Langlands.Weil.Local.DegreeCharacters
Langlands.Weil.Local.Parameters
Langlands.Weil.Local.ResidueCharacters
Langlands.Weil.Pullback
Langlands.Weil.Representation.Basic
Langlands.Weil.Representation.CharacterLine
Langlands.Weil.Representation.Continuity
Langlands.Weil.Representation.ContinuityProof
Langlands.Weil.Representation.Determinant
Langlands.Weil.Representation.DirectSum
Langlands.Weil.Representation.Dual
Langlands.Weil.Representation.DualClasses
Langlands.Weil.Representation.IsomorphismInvarianceProof
Langlands.Weil.Representation.OperationClosureProof
Langlands.Weil.Representation.Operations
Langlands.Weil.Representation.Predicates
Langlands.Weil.Representation.Twist
Langlands.Weil.Representation.TwistClasses
Langlands.Weil.Representation.TwistProperties
Langlands.Weil.Topology
Langlands.Weil.TopologyProof
Langlands.WeilDeligne.Basic
Langlands.WeilDeligne.DirectSum
Langlands.WeilDeligne.Dual
Langlands.WeilDeligne.ParameterRelations
Langlands.WeilDeligne.Parameters
Langlands.WeilDeligne.Twist
```

### External frontier imports

```text
Lean.Elab.Tactic.Omega
Mathlib.Algebra.Algebra.Bilinear
Mathlib.Algebra.Algebra.NonUnitalHom
Mathlib.Algebra.Algebra.NonUnitalSubalgebra
Mathlib.Algebra.Algebra.Subalgebra.Lattice
Mathlib.Algebra.BigOperators.Fin
Mathlib.Algebra.BigOperators.Finprod
Mathlib.Algebra.BigOperators.Group.Finset.Basic
Mathlib.Algebra.BigOperators.Group.List.Basic
Mathlib.Algebra.BigOperators.GroupWithZero.Action
Mathlib.Algebra.BigOperators.Pi
Mathlib.Algebra.Category.ModuleCat.Basic
Mathlib.Algebra.CharP.Basic
Mathlib.Algebra.DirectSum.Module
Mathlib.Algebra.Exact.Basic
Mathlib.Algebra.Field.Subfield.Basic
Mathlib.Algebra.Group.Hom.Instances
Mathlib.Algebra.Group.Pi.Lemmas
Mathlib.Algebra.Group.Subgroup.Ker
Mathlib.Algebra.Group.Subgroup.Pointwise
Mathlib.Algebra.Group.Submonoid.Basic
Mathlib.Algebra.Group.TypeTags.Finite
Mathlib.Algebra.Group.TypeTags.Hom
Mathlib.Algebra.Module.LinearMap.FiniteRange
Mathlib.Algebra.Module.PID
Mathlib.Algebra.Module.Submodule.Map
Mathlib.Algebra.Order.Archimedean.Basic
Mathlib.Algebra.Order.BigOperators.Group.Finset
Mathlib.Algebra.Polynomial.FieldDivision
Mathlib.Algebra.Polynomial.Lifts
Mathlib.Algebra.Polynomial.Module.AEval
Mathlib.Algebra.Polynomial.Module.FiniteDimensional
Mathlib.Algebra.Ring.GeomSum
Mathlib.Analysis.Complex.Basic
Mathlib.Analysis.Complex.Cardinality
Mathlib.Analysis.Complex.Circle
Mathlib.Analysis.Complex.Polynomial.Basic
Mathlib.Analysis.InnerProductSpace.Defs
Mathlib.Analysis.Matrix.MeasurableSpace
Mathlib.Analysis.Matrix.Normed
Mathlib.Analysis.MeanInequalitiesPow
Mathlib.Analysis.Normed.Module.FiniteDimension
Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
Mathlib.Analysis.Normed.Unbundled.SpectralNorm
Mathlib.Analysis.Real.Sqrt
Mathlib.Analysis.SpecialFunctions.Complex.Circle
Mathlib.Analysis.SpecialFunctions.Pow.NNReal
Mathlib.Analysis.SpecialFunctions.Pow.Real
Mathlib.Analysis.SpecialFunctions.Sqrt
Mathlib.Analysis.SpecificLimits.Basic
Mathlib.Basic.Complex.Basic
Mathlib.CategoryTheory.Discrete.Basic
Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
Mathlib.CategoryTheory.Pi.Basic
Mathlib.CategoryTheory.Skeletal
Mathlib.CategoryTheory.Whiskering
Mathlib.Combinatorics.Enumerative.Composition
Mathlib.Data.ENat.BigOperators
Mathlib.Data.Fin.Rev
Mathlib.Data.Fin.Tuple.Sort
Mathlib.Data.Fintype.EquivFin
Mathlib.Data.Fintype.Quotient
Mathlib.Data.Fintype.Sort
Mathlib.Data.Int.Cast.Lemmas
Mathlib.Data.Int.Interval
Mathlib.Data.Int.LeastGreatest
Mathlib.Data.List.FinRange
Mathlib.Data.List.Pairwise
Mathlib.Data.List.TakeDrop
Mathlib.Data.Matrix.Basic
Mathlib.Data.Matrix.Block
Mathlib.Data.Nat.Find
Mathlib.Data.PNat.Basic
Mathlib.Data.Set.Card
Mathlib.Data.Set.Finite.Basic
Mathlib.Data.Sym.Basic
Mathlib.Data.ZMod.Basic
Mathlib.FieldTheory.AbsoluteGaloisGroup
Mathlib.FieldTheory.Finite.Basic
Mathlib.FieldTheory.Finite.Extension
Mathlib.FieldTheory.Galois.Profinite
Mathlib.FieldTheory.PrimitiveElement
Mathlib.GroupTheory.Abelianization.Defs
Mathlib.GroupTheory.Coset.Defs
Mathlib.GroupTheory.DoubleCoset
Mathlib.GroupTheory.FiniteIndexNormalSubgroup
Mathlib.GroupTheory.GroupAction.Basic
Mathlib.GroupTheory.GroupAction.ConjAct
Mathlib.GroupTheory.GroupAction.Defs
Mathlib.GroupTheory.GroupAction.Quotient
Mathlib.GroupTheory.Index
Mathlib.GroupTheory.OrderOfElement
Mathlib.GroupTheory.QuotientGroup.Defs
Mathlib.GroupTheory.Subgroup.Centralizer
Mathlib.GroupTheory.Transfer
Mathlib.LinearAlgebra.AnnihilatingPolynomial
Mathlib.LinearAlgebra.Basis.VectorSpace
Mathlib.LinearAlgebra.BilinearForm.Properties
Mathlib.LinearAlgebra.Charpoly.Basic
Mathlib.LinearAlgebra.Charpoly.ToMatrix
Mathlib.LinearAlgebra.Determinant
Mathlib.LinearAlgebra.Dimension.Basic
Mathlib.LinearAlgebra.Dimension.Constructions
Mathlib.LinearAlgebra.Dimension.StrongRankCondition
Mathlib.LinearAlgebra.DirectSum.Finite
Mathlib.LinearAlgebra.Dual.Defs
Mathlib.LinearAlgebra.Dual.Lemmas
Mathlib.LinearAlgebra.Eigenspace.Pi
Mathlib.LinearAlgebra.Eigenspace.Triangularizable
Mathlib.LinearAlgebra.FiniteDimensional.Basic
Mathlib.LinearAlgebra.FiniteDimensional.Defs
Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
Mathlib.LinearAlgebra.Finsupp.LinearCombination
Mathlib.LinearAlgebra.Finsupp.VectorSpace
Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
Mathlib.LinearAlgebra.Isomorphisms
Mathlib.LinearAlgebra.Matrix.BilinearForm
Mathlib.LinearAlgebra.Matrix.Block
Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
Mathlib.LinearAlgebra.Matrix.Charpoly.Univ
Mathlib.LinearAlgebra.Matrix.Diagonal
Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
Mathlib.LinearAlgebra.Matrix.Kronecker
Mathlib.LinearAlgebra.Matrix.Permutation
Mathlib.LinearAlgebra.Matrix.Reindex
Mathlib.LinearAlgebra.Matrix.SchurComplement
Mathlib.LinearAlgebra.Matrix.Transvection
Mathlib.LinearAlgebra.PiTensorProduct.Basic
Mathlib.LinearAlgebra.PiTensorProduct.Basis
Mathlib.LinearAlgebra.PiTensorProduct.Dual
Mathlib.LinearAlgebra.PiTensorProduct.Finite
Mathlib.LinearAlgebra.PiTensorProduct.Generators
Mathlib.LinearAlgebra.Projection
Mathlib.LinearAlgebra.Quotient.Basic
Mathlib.LinearAlgebra.Semisimple
Mathlib.LinearAlgebra.TensorProduct.Basis
Mathlib.LinearAlgebra.TensorProduct.RightExactness
Mathlib.LinearAlgebra.Trace
Mathlib.Logic.Equiv.Fin.Basic
Mathlib.MeasureTheory.Constructions.Pi
Mathlib.MeasureTheory.Function.LocallyIntegrable
Mathlib.MeasureTheory.Function.LpSeminorm.Defs
Mathlib.MeasureTheory.Function.SimpleFunc
Mathlib.MeasureTheory.Group.Integral
Mathlib.MeasureTheory.Group.LIntegral
Mathlib.MeasureTheory.Group.Measure
Mathlib.MeasureTheory.Group.ModularCharacter
Mathlib.MeasureTheory.Integral.Bochner.Basic
Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
Mathlib.MeasureTheory.Integral.Bochner.Set
Mathlib.MeasureTheory.Integral.Marginal
Mathlib.MeasureTheory.Integral.Prod
Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
Mathlib.MeasureTheory.Measure.Haar.Basic
Mathlib.MeasureTheory.Measure.Haar.DistribChar
Mathlib.MeasureTheory.Measure.Haar.MulEquivHaarChar
Mathlib.MeasureTheory.Measure.Haar.Unique
Mathlib.MeasureTheory.Measure.OpenPos
Mathlib.MeasureTheory.Measure.Regular
Mathlib.MeasureTheory.Measure.Typeclasses.Finite
Mathlib.NumberTheory.LocalField.Basic
Mathlib.NumberTheory.Padics.LocalField
Mathlib.NumberTheory.Padics.RingHoms
Mathlib.Order.Atoms
Mathlib.Order.Hom.Set
Mathlib.Order.Interval.Finset.Fin
Mathlib.Order.WithBot
Mathlib.RepresentationTheory.Basic
Mathlib.RepresentationTheory.Coinduced
Mathlib.RepresentationTheory.Coinvariants
Mathlib.RepresentationTheory.Equiv
Mathlib.RepresentationTheory.Intertwining
Mathlib.RepresentationTheory.Invariants
Mathlib.RepresentationTheory.Irreducible
Mathlib.RepresentationTheory.Rep.Basic
Mathlib.RepresentationTheory.Rep.Res
Mathlib.RepresentationTheory.Semisimple
Mathlib.RepresentationTheory.Subrepresentation
Mathlib.RingTheory.Adjoin.Basic
Mathlib.RingTheory.Adjoin.Polynomial.Basic
Mathlib.RingTheory.AdjoinRoot
Mathlib.RingTheory.Algebraic.LinearIndependent
Mathlib.RingTheory.Artinian.Module
Mathlib.RingTheory.DedekindDomain.IntegralClosure
Mathlib.RingTheory.FiniteLength
Mathlib.RingTheory.Finiteness.Basic
Mathlib.RingTheory.Finiteness.Defs
Mathlib.RingTheory.Finiteness.Finsupp
Mathlib.RingTheory.Flat.Basic
Mathlib.RingTheory.Ideal.Quotient.Basic
Mathlib.RingTheory.Ideal.Quotient.Operations
Mathlib.RingTheory.Length
Mathlib.RingTheory.Nakayama
Mathlib.RingTheory.Nilpotent.Basic
Mathlib.RingTheory.Noetherian.Basic
Mathlib.RingTheory.Noetherian.Defs
Mathlib.RingTheory.Norm.Transitivity
Mathlib.RingTheory.Polynomial.Basic
Mathlib.RingTheory.Polynomial.UniqueFactorization
Mathlib.RingTheory.PowerBasis
Mathlib.RingTheory.PrincipalIdealDomain
Mathlib.RingTheory.RamificationInertia.Basic
Mathlib.RingTheory.SimpleModule.Basic
Mathlib.RingTheory.Valuation.Extension
Mathlib.RingTheory.Valuation.Integral
Mathlib.RingTheory.Valuation.LocalSubring
Mathlib.RingTheory.Valuation.RamificationGroup
Mathlib.Tactic
Mathlib.Tactic.Group
Mathlib.Tactic.Linarith
Mathlib.Tactic.NoncommRing
Mathlib.Tactic.NormNum
Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
Mathlib.Topology.Algebra.ClopenNhdofOne
Mathlib.Topology.Algebra.ConstMulAction
Mathlib.Topology.Algebra.ContinuousMonoidHom
Mathlib.Topology.Algebra.Group.Basic
Mathlib.Topology.Algebra.Group.ClosedSubgroup
Mathlib.Topology.Algebra.Group.Matrix
Mathlib.Topology.Algebra.Group.Neighborhood
Mathlib.Topology.Algebra.Group.OpenMapping
Mathlib.Topology.Algebra.Group.Pointwise
Mathlib.Topology.Algebra.Group.Quotient
Mathlib.Topology.Algebra.Group.Subgroup
Mathlib.Topology.Algebra.Group.Units
Mathlib.Topology.Algebra.GroupWithZero
Mathlib.Topology.Algebra.Module.FiniteDimension
Mathlib.Topology.Algebra.Module.ModuleTopology
Mathlib.Topology.Algebra.MulAction
Mathlib.Topology.Algebra.MvPolynomial
Mathlib.Topology.Algebra.Nonarchimedean.Basic
Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected
Mathlib.Topology.Algebra.OpenSubgroup
Mathlib.Topology.Algebra.ProperAction.Basic
Mathlib.Topology.Algebra.Ring.Compact
Mathlib.Topology.Algebra.Ring.Ideal
Mathlib.Topology.Algebra.Support
Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology
Mathlib.Topology.Algebra.Valued.NormedValued
Mathlib.Topology.Baire.Lemmas
Mathlib.Topology.Baire.LocallyCompactRegular
Mathlib.Topology.Bases
Mathlib.Topology.Compactness.Compact
Mathlib.Topology.Compactness.LocallyCompact
Mathlib.Topology.Compactness.SigmaCompact
Mathlib.Topology.Connected.TotallyDisconnected
Mathlib.Topology.ContinuousMap.CompactlySupported
Mathlib.Topology.Homeomorph.Lemmas
Mathlib.Topology.Homeomorph.Quotient
Mathlib.Topology.Instances.Int
Mathlib.Topology.Instances.Matrix
Mathlib.Topology.Instances.NNReal.Lemmas
Mathlib.Topology.LocallyClosed
Mathlib.Topology.LocallyConstant.Algebra
Mathlib.Topology.LocallyConstant.Basic
Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
Mathlib.Topology.Order.Compact
Mathlib.Topology.Separation.Profinite
Mathlib.Topology.UrysohnsLemma
```
