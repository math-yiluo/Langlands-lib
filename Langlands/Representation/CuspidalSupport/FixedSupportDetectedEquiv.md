# Actual equivalences between detected constituents with fixed support

Author: Worker 357.

This internal constructor composes published constituent equivalences and
published factor matching under cuspidal association. It returns an actual
representation equivalence for two positive-rank objects with the same
supercuspidal support and nonzero full top derivatives. It introduces no
additional literature assertion or assumed generic uniqueness theorem.

## Exact interface

The outer parameters are every prime `p` with `Fact p.Prime`, an actual
`F : PadicField.{uF} p`, supplied `T : F.TopologicalData`, and a bundled
continuous nontrivial unitary additive character `ψ` for `T.topology`.
The field universe `uF` and original supercuspidal carrier universe `uV`
are independent.

`Langlands.CuspidalSupport.fixedSupportDetectedEquiv T ψ hn D E s hD hE hJD hJE`
has the following inputs:

- A positive total rank `n`, with `hn : 0 < n`.
- Actual smooth objects `D` and `E` on `GL_n(F)`, both in carrier universe
  `max uF uV` and using the supplied topology.
- One multiset `s : Multiset (CuspidalDatum.{uV,uF} T)`.
- `hD : T.IsSupercuspidalSupport D s` and
  `hE : T.IsSupercuspidalSupport E s`.
- Nontriviality of both actual images under
  `Derivative.generalLinearDerivative T ψ n n le_rfl` at the common carrier
  universe `max uF uV`.

It returns `D.representation.Equiv E.representation`: an equivariant complex
linear equivalence with both inverse identities. The support hypotheses
already include irreducibility, by the existing definition of
`IsCuspidalConstituent`. The constructor adds no finite-length, association,
composition-series, representative-choice or top-line premise. It does
require the displayed top-derivative nontriviality for each of `D` and `E`.
It makes no assertion of nontriviality for another constituent.

The unsaturated original universe `uV` in the support is retained. The
supercuspidal representatives have carriers in `Type uV`; their normalized
induced objects and `D`, `E`, and their derivatives have carriers in
`Type (max uF uV)`. All derivatives appearing in this constructor use that
same latter universe. No comparison of derivative functors in different
carrier universes occurs. Repeated cuspidal data are allowed.

## Implemented finite-index and constituent adapters

`count_ofFn_eq_sum` writes the occurrence count of a value in `List.ofFn f`
as the finite sum of its equality indicators. Induction over the index
cardinality expands the first list entry and the first finite-sum term.
`fiber_card` rewrites the indicator sum as the cardinality of the corresponding
finite fiber. Equality of the two multiset lists therefore gives equal fiber
cardinalities. The noncomputable `reindexingOfMultiset` uses
`Fintype.equivOfCardEq` on every fiber, then `Equiv.ofFiberEquiv`, to return
an actual equivalence of the two index sets preserving the indexed value.
Each occurrence remains an index, including equal occurrences.

`subquotient_of_matching` transfers a given irreducible smooth subquotient
between two objects with `HaveSameJordanHolderFactors`. Unpack their actual
matching composition series. The published `simpleSubquotientFactor`
identifies the given irreducible subquotient with a grade of the first series.
Compose that equivalence with the supplied matching grade equivalence. The
matching grade of the second series is its actual smooth subquotient by
`smoothGradedObject_isSubquotient`. Transport along the inverse of the
composed equivalence with `SmoothRep.IsSubquotient.of_iso_left`.

`cuspidalProduct_factors_permute` specializes the published general
cuspidal-association factor theorem to a supplied block permutation `e`.
Its source Levi object is the external smooth tensor of the given actual
supercuspidal factors `A i`. Its target is the external smooth tensor of
`A (e i)` on `B.permute e`. The published `glCuspidalTensor` supplies
irreducibility and actual Levi cuspidality for both tensors. The actual
associating permutation is `B.blockPermutation e`; the published
`conjugatesLevi_blockPermutation` proves that it conjugates the whole Levi.
The actual equivalence in the association witness is exactly
`blockPermutationTensorEquiv`, retaining the inverse-conjugation convention
of `CuspidalSupport.transport`.

Apply `associatedCuspidalInductionFactorsTheorem` to those two tensors.
Their canonical normalized parabolic inductions are definitionally the
normalized product inductions displayed in the helper's target. Thus this
step supplies multiplicity-sensitive matching of actual composition series.
It does not assume commutativity as an actual induced-object isomorphism.

## Constructing the final equivalence

The two support witnesses give ordered families `ρ : Fin k → CuspidalDatum T`
and `ρ' : Fin l → CuspidalDatum T`, their rank sums `h` and `h'`, actual
supercuspidal representatives `A` and `A'`, proofs that these represent the
displayed data, and actual subquotient occurrences for `D` and `E`.
Both multiset lists equal `s`. Taking multiset cardinalities proves `k = l`.
After eliminating that equality, `reindexingOfMultiset ρ' ρ` gives a
permutation `e` with `ρ (e i) = ρ' i`. Substitute the resulting function
equality for `ρ'`.

The published `T.cuspidalProductInducedIsoOfRepresented` transports `E`'s
occurrence from the given representatives `A' i` to the representatives
`A (e i)` of those same reordered data. All normalization characters, upper
parabolics and right-translation actions are the existing ones.
The shape `T.cuspidalShape (fun i => ρ (e i)) h'` is definitionally
`(T.cuspidalShape ρ h).permute e`; the rank-sum proofs are proof-irrelevant.
The factor-permutation helper and symmetry of matching factors then move
`E`'s occurrence to the one fixed ordered product
`P := T.cuspidalProductInduced ρ h A`.

Choose `c := Derivative.chooseCuspidalProductDetectedConstituent T ψ hn
(T.cuspidalShape ρ h) A`. This published constructor supplies actual
`ExactFunctorDetectedConstituent.Data` for the same `P` and full top
functor. Its `equivalence` field returns actual equivalences from its selected
constituent to every irreducible subquotient of `P` whose top image is
nontrivial. Apply it to `D` and to the transferred occurrence of `E`, using
exactly `hJD` and `hJE`. Invert the first equivalence and compose with the
second. This is the returned actual map.

The implementation first constructs `Nonempty` of the result, so the
existential support witnesses are eliminated only into `Prop`; the final
`Classical.choice` supplies the actual equivalence. All choices are
noncomputable.

## Published dependency and independence audit

The four direct project imports are
`Derivative.CuspidalProductDetectedConstituent`,
`CuspidalSupport.AssociationForwardFactorsProof`,
`CuspidalSupport.BlockPermutationTensor`, and
`CuspidalSupport.CuspidalTensorProof`. The two direct Mathlib imports are
`Data.Fintype.EquivFin` and `Algebra.BigOperators.Ring.Finset`.
All inherited Lean/Markdown pairs match published Library
`83a867912d2befca2ebf3e208f7d8fc29ae19ec5` byte for byte.
There is no pending or draft input in this construction.

The author read the four primary project pairs and the displayed definitions
of association, transport, external tensors, support, and the detected
constituent API. The association branch proves the general forward
factor-matching implication by adjacent Levi block swaps and Jordan–Hölder
comparison. The tensor branch proves actual Weyl transport by dependent tensor
reindexing and tensor irreducibility/cuspidality from factor properties.
These branches introduce no derivative or segment formula.
The detected-constituent branch uses the previously audited general exact
functor argument, scalar top derivative of a fixed cuspidal product, proved
cuspidal-only top nonvanishing, general derivative exactness and Leibniz
comparison, Whittaker multiplicity one, and finite length of products of
irreducible factors. Its used bodies and complete closure remain the
published ones. This is a used-body audit together with recursive import,
byte-equality and code scans, not a claim to have reread every inherited file.

The recursive closure inventory below has 944 project modules, including
this new module, and 289 external frontier imports. There are no missing
project modules or missing/empty paired Markdown files. All 943 inherited
pairs equal the named Library. Searches on Lean with comments and string
literals removed found no prohibited execution syntax, proof holes, new
axioms, or the host's scanned excluded declaration names and task identifiers.
The only `Classification` modules in this closure are individual
supercuspidal, generic support/constituent and general finite-length/product
embedding infrastructure and their statement definitions. No individual-head
construction is needed by this new adapter.

The audited closure contains none of the parent generic segment-product
uniqueness, multisegment exhaustion, ordered strong-head existence, quotient
coverage, ordered conversion, tempered uniqueness, square-integrable
classification/exhaustion or regular exhaustion conclusions. It contains no
Ze80 3.5/9.6 segment derivative formula or proof successor, full segment
Jacquet formula, segment-socle derivative argument or restricted support-proof
intermediate. In particular it does not import `SegmentHeadSupportStep`,
`SegmentHeadJacquetReduction`, `TwoSupercuspidalProductStructureProof`, or
use `core_mid`.

The host's complete trusted operator rulings
`bd71b9185aab5d6eafffb7891bd3a3ca`,
`0edda6122ce65ed7ac51603c37473920`,
`30144f6f9b59540b88b6d4c1517892d9`,
`ed80148e21e7523abfc048f455e98eb0`,
`2b33898bdd0a5ff1b9031be5155a06f0`, and
`ca18fd5005bf5e12a3f7cade18dca865` were read in full.
The first two permit the proved general derivative foundations while
preserving the host's independence exclusions. This construction needs no
support-only bound, no restricted length-two intermediate, and no restricted
adjacent-supercuspidal reducibility exception from the later rulings.

## Scope and development evidence

This is an actual equivalence constructor obtained by composing the
published generic interfaces. It is not a proposition declaration for an
unproved uniqueness assertion. It does not prove nontriviality of any
additional top derivative, irreducibility of a product, existence of special
heads, a truncated-head identification, or a segment derivative formula.
It neither proves nor completes either direction of the host
`SegmentHeadProductIrreducibility` criterion. Its own publication requires
independent semantic review and integration.

Development compilation and exact declaration inspection completed with no
errors or warnings. Inspection reports a definition with precisely universe
parameters `uF`, `uV` and only `propext`, `Classical.choice`, and `Quot.sound`.
Development checks and this author audit do not establish independent
mathematical acceptance.

## Complete recursive project import inventory

Each item is a Lean module name. Every inherited module's same-stem Markdown
pair was included in the byte-equality audit. The first inventory includes
this entry module.

- `Langlands.Algebra.CommutingDimensionHelpers`
- `Langlands.Algebra.CommutingDimensionNilpotent`
- `Langlands.Algebra.CommutingDimensionNumerics`
- `Langlands.Algebra.CommutingDimensionPrimary`
- `Langlands.Algebra.CommutingDimensionRecurrence`
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
- `Langlands.Group.GL.BlockUnipotent`
- `Langlands.Group.GL.BlockUnipotentCoordinates`
- `Langlands.Group.GL.BlockUnipotentHaarProof`
- `Langlands.Group.GL.BlockUnipotentHaarStatement`
- `Langlands.Group.GL.Blocks`
- `Langlands.Group.GL.CartanProof`
- `Langlands.Group.GL.CartanStatement`
- `Langlands.Group.GL.CompactOpen`
- `Langlands.Group.GL.CountabilityProof`
- `Langlands.Group.GL.CountabilityStatement`
- `Langlands.Group.GL.DominantExponentGeneration`
- `Langlands.Group.GL.HeadTailBlocks`
- `Langlands.Group.GL.IntegralSubgroup`
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
- `Langlands.Group.GL.Nonarchimedean`
- `Langlands.Group.GL.NonarchimedeanStatement`
- `Langlands.Group.GL.NormalizedCharacter`
- `Langlands.Group.GL.OneBlockShape`
- `Langlands.Group.GL.OppositeBlocks`
- `Langlands.Group.GL.Padic`
- `Langlands.Group.GL.PadicBlocks`
- `Langlands.Group.GL.PadicOppositeBlocks`
- `Langlands.Group.GL.PadicUpperUnipotent`
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
- `Langlands.HarmonicAnalysis.RowFourier`
- `Langlands.HarmonicAnalysis.RowTensorDecompositionProof`
- `Langlands.HarmonicAnalysis.RowTensorDecompositionStatement`
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
- `Langlands.LocalField.Topology`
- `Langlands.LocalField.Uniformizer`
- `Langlands.Representation.Category.Abelian`
- `Langlands.Representation.Category.Basic`
- `Langlands.Representation.Category.ClassInvariants`
- `Langlands.Representation.Category.ConstituentDichotomy`
- `Langlands.Representation.Category.ConstituentDichotomyStatement`
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
- `Langlands.Representation.Classification.ConstituentRelations`
- `Langlands.Representation.Classification.FiniteLengthProof`
- `Langlands.Representation.Classification.FiniteLengthStatement`
- `Langlands.Representation.Classification.IrreducibleProductEmbedding`
- `Langlands.Representation.Classification.IrreducibleProductEmbeddingStatement`
- `Langlands.Representation.Classification.IrreducibleProductFiniteLengthProof`
- `Langlands.Representation.Classification.NormalizedProductFiniteLengthStatement`
- `Langlands.Representation.Classification.Segments`
- `Langlands.Representation.Classification.Supercuspidal`
- `Langlands.Representation.Classification.SupercuspidalContragredientAux`
- `Langlands.Representation.Classification.SupercuspidalContragredientStatement`
- `Langlands.Representation.Classification.SupercuspidalDerivativeVanishing`
- `Langlands.Representation.Classification.SupercuspidalDerivativesProof`
- `Langlands.Representation.Classification.SupercuspidalDerivativesStatement`
- `Langlands.Representation.Classification.SupercuspidalSupport`
- `Langlands.Representation.Classification.SupercuspidalTopDerivative`
- `Langlands.Representation.Classification.SupercuspidalTwist`
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
- `Langlands.Representation.CuspidalSupport.AdjacentMatchingAssembly`
- `Langlands.Representation.CuspidalSupport.AdjacentMergedTensor`
- `Langlands.Representation.CuspidalSupport.AdjacentSwapProof`
- `Langlands.Representation.CuspidalSupport.AdjacentSwapStatement`
- `Langlands.Representation.CuspidalSupport.AdjacentTensorReduction`
- `Langlands.Representation.CuspidalSupport.AssociatedAssembly`
- `Langlands.Representation.CuspidalSupport.AssociatedConditional`
- `Langlands.Representation.CuspidalSupport.AssociatedGeometricPieceVanishingProof`
- `Langlands.Representation.CuspidalSupport.AssociatedGeometricPiecesEquivalenceProof`
- `Langlands.Representation.CuspidalSupport.AssociatedGeometricPiecesProof`
- `Langlands.Representation.CuspidalSupport.AssociatedGeometricPiecesStatement`
- `Langlands.Representation.CuspidalSupport.AssociatedProof`
- `Langlands.Representation.CuspidalSupport.AssociatedRankZero`
- `Langlands.Representation.CuspidalSupport.AssociationForwardFactorsProof`
- `Langlands.Representation.CuspidalSupport.AssociationForwardHomProof`
- `Langlands.Representation.CuspidalSupport.AssociationForwardHomSupport`
- `Langlands.Representation.CuspidalSupport.AssociationForwardStatement`
- `Langlands.Representation.CuspidalSupport.AssociationLawsProof`
- `Langlands.Representation.CuspidalSupport.AssociationLawsStatement`
- `Langlands.Representation.CuspidalSupport.AssociationReduction`
- `Langlands.Representation.CuspidalSupport.BlockMap`
- `Langlands.Representation.CuspidalSupport.BlockPermutation`
- `Langlands.Representation.CuspidalSupport.BlockPermutationTensor`
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
- `Langlands.Representation.CuspidalSupport.DualAveraging`
- `Langlands.Representation.CuspidalSupport.FiltrationQuasicuspidality`
- `Langlands.Representation.CuspidalSupport.FiniteBlockShapes`
- `Langlands.Representation.CuspidalSupport.FixedSupportDetectedEquiv`
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
- `Langlands.Representation.CuspidalSupport.StandardJacquetComparisonProof`
- `Langlands.Representation.CuspidalSupport.TotalConjugatingCountProof`
- `Langlands.Representation.CuspidalSupport.TotalConjugatingCountStatement`
- `Langlands.Representation.CuspidalSupport.TwoBlockAssociationProof`
- `Langlands.Representation.CuspidalSupport.ZeroRankEmbeddingProof`
- `Langlands.Representation.Derivative.CuspidalProductDetectedConstituent`
- `Langlands.Representation.Derivative.FiniteTopLine`
- `Langlands.Representation.Derivative.GeneralLinearDerivativeExactnessProof`
- `Langlands.Representation.Derivative.GeneralLinearDerivativeExactnessStatement`
- `Langlands.Representation.Derivative.GeneralLinearDerivativeLeibnizBoundary`
- `Langlands.Representation.Derivative.GeneralLinearDerivativeLeibnizFiltrationProof`
- `Langlands.Representation.Derivative.GeneralLinearDerivativeLeibnizFiltrationStatement`
- `Langlands.Representation.Derivative.Homogeneity`
- `Langlands.Representation.Derivative.Iteration`
- `Langlands.Representation.Derivative.LeftMixedProductDerivativeProof`
- `Langlands.Representation.Derivative.LeftMixedProductHigher`
- `Langlands.Representation.Derivative.LeftMixedProductVanishing`
- `Langlands.Representation.Derivative.LeftMixedProductZeroRank`
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
- `Langlands.Representation.Derivative.MirabolicDerivativeVanishing`
- `Langlands.Representation.Derivative.MirabolicDeterminant`
- `Langlands.Representation.Derivative.MirabolicLatticeBox`
- `Langlands.Representation.Derivative.MirabolicMinus`
- `Langlands.Representation.Derivative.MirabolicMinusExactnessProof`
- `Langlands.Representation.Derivative.MirabolicMinusExactnessStatement`
- `Langlands.Representation.Derivative.MirabolicMixedOrbitCharacters`
- `Langlands.Representation.Derivative.MirabolicPhiMinusMackey`
- `Langlands.Representation.Derivative.MirabolicPlus`
- `Langlands.Representation.Derivative.MirabolicProductMinusBoundary`
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
- `Langlands.Representation.Derivative.MixedProductDerivativeStatement`
- `Langlands.Representation.Derivative.MixedProductRankCast`
- `Langlands.Representation.Derivative.OrderRecursion`
- `Langlands.Representation.Derivative.RankCastCompat`
- `Langlands.Representation.Derivative.RightMixedProductDerivativeFiltrationProof`
- `Langlands.Representation.Derivative.RightMixedProductDerivativeFiltrationStatement`
- `Langlands.Representation.Derivative.RightMixedProductDerivativePositive`
- `Langlands.Representation.Derivative.RightMixedProductZeroRank`
- `Langlands.Representation.Derivative.ShortExactFunctorLaws`
- `Langlands.Representation.Derivative.TopLine`
- `Langlands.Representation.Derivative.TopProduct`
- `Langlands.Representation.Derivative.ZeroRankTensor`
- `Langlands.Representation.Dual.Definitions`
- `Langlands.Representation.Exponents.ParabolicPair`
- `Langlands.Representation.Filtration.ActualGradedExtraction`
- `Langlands.Representation.Filtration.CoinvariantVanishingStatement`
- `Langlands.Representation.Filtration.Definitions`
- `Langlands.Representation.Filtration.ExactConstituentExtraction`
- `Langlands.Representation.Filtration.ExactFunctorDetectedConstituent`
- `Langlands.Representation.Filtration.ExactFunctorIrreducibility`
- `Langlands.Representation.Filtration.ExactSmoothSubquotients`
- `Langlands.Representation.Filtration.ExactSmoothTransport`
- `Langlands.Representation.Filtration.FactorMatchingPullback`
- `Langlands.Representation.Filtration.GluedFamily`
- `Langlands.Representation.Filtration.GradedRefinementProof`
- `Langlands.Representation.Filtration.GradedRefinementStatement`
- `Langlands.Representation.Filtration.IntervalLiftProof`
- `Langlands.Representation.Filtration.IntervalLiftStatement`
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
- `Langlands.Representation.Filtration.ObjectDefinitions`
- `Langlands.Representation.Filtration.OneStep`
- `Langlands.Representation.Filtration.Precomposition`
- `Langlands.Representation.Filtration.QuasicuspidalVanishingProof`
- `Langlands.Representation.Filtration.QuotientFirstIso`
- `Langlands.Representation.Filtration.QuotientTail`
- `Langlands.Representation.Filtration.RepresentationLength`
- `Langlands.Representation.Filtration.SimpleSubquotientFactorProof`
- `Langlands.Representation.Filtration.SimpleSubquotientFactorStatement`
- `Langlands.Representation.Filtration.SingletonIso`
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
- `Langlands.Representation.Induction.BlockEquivalence`
- `Langlands.Representation.Induction.BlockFactors`
- `Langlands.Representation.Induction.CharacterTwistProof`
- `Langlands.Representation.Induction.CompactAutomorphism`
- `Langlands.Representation.Induction.CompactAutomorphismIntegralProof`
- `Langlands.Representation.Induction.CompactAutomorphismIntegralStatement`
- `Langlands.Representation.Induction.CompactCoinvariantBijectivityProof`
- `Langlands.Representation.Induction.CompactCoinvariantBijectivityStatement`
- `Langlands.Representation.Induction.CompactCoinvariantIntegral`
- `Langlands.Representation.Induction.CompactCoinvariantLocalInverseProof`
- `Langlands.Representation.Induction.CompactCoinvariantLocalInverseStatement`
- `Langlands.Representation.Induction.CompactLocalSection`
- `Langlands.Representation.Induction.CompactLocalSectionSpanningProof`
- `Langlands.Representation.Induction.CompactLocalSectionSpanningStatement`
- `Langlands.Representation.Induction.CompactLocallyConstant`
- `Langlands.Representation.Induction.CompactQuotientCutoff`
- `Langlands.Representation.Induction.CompactQuotientProof`
- `Langlands.Representation.Induction.CompactSurjectivityProof`
- `Langlands.Representation.Induction.CompactSurjectivityStatement`
- `Langlands.Representation.Induction.CompactTransitivityProof`
- `Langlands.Representation.Induction.CompactTransitivityStatement`
- `Langlands.Representation.Induction.ConjugateParabolic`
- `Langlands.Representation.Induction.Definitions`
- `Langlands.Representation.Induction.Equivalences`
- `Langlands.Representation.Induction.FiniteProductTensor`
- `Langlands.Representation.Induction.FiniteProductTensorBijectiveProof`
- `Langlands.Representation.Induction.FiniteProductTensorBijectiveStatement`
- `Langlands.Representation.Induction.HeterogeneousConstruction`
- `Langlands.Representation.Induction.HeterogeneousPairs`
- `Langlands.Representation.Induction.InverseTranspose`
- `Langlands.Representation.Induction.NormalCoinvariantKernelProof`
- `Langlands.Representation.Induction.NormalCoinvariantKernelStatement`
- `Langlands.Representation.Induction.NormalCoinvariantMap`
- `Langlands.Representation.Induction.NormalCoinvariantProof`
- `Langlands.Representation.Induction.NormalCoinvariantStatement`
- `Langlands.Representation.Induction.NormalSplitComparison`
- `Langlands.Representation.Induction.OppositeParabolic`
- `Langlands.Representation.Induction.Parabolic`
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
- `Langlands.Representation.Jacquet.CanonicalLiftStatement`
- `Langlands.Representation.Jacquet.CharacterAveraging`
- `Langlands.Representation.Jacquet.CharacterTwistEquiv`
- `Langlands.Representation.Jacquet.Coinvariants`
- `Langlands.Representation.Jacquet.CompressionStabilizationProof`
- `Langlands.Representation.Jacquet.CompressionStabilizationStatement`
- `Langlands.Representation.Jacquet.ExactProof`
- `Langlands.Representation.Jacquet.ExactStatement`
- `Langlands.Representation.Jacquet.Localization`
- `Langlands.Representation.Jacquet.LocalizationExactnessProof`
- `Langlands.Representation.Jacquet.LocalizationExactnessStatement`
- `Langlands.Representation.Jacquet.LocalizationTransport`
- `Langlands.Representation.Jacquet.Normalized`
- `Langlands.Representation.Jacquet.Parabolic`
- `Langlands.Representation.Jacquet.PositiveCharacter`
- `Langlands.Representation.Jacquet.ReciprocityProof`
- `Langlands.Representation.Jacquet.ReciprocityStatement`
- `Langlands.Representation.Jacquet.SmoothTwist`
- `Langlands.Representation.MatrixCoefficient.Definitions`
- `Langlands.Representation.MatrixCoefficient.LawsProof`
- `Langlands.Representation.MatrixCoefficient.LawsStatement`
- `Langlands.Representation.Mirabolic.LeftMixedProductSuccessor`
- `Langlands.Representation.Mirabolic.MixedProducts`
- `Langlands.Representation.OrbitSpan`
- `Langlands.Representation.Parabolic.AdmissibilityStatement`
- `Langlands.Representation.Parabolic.ComposedFunctors`
- `Langlands.Representation.Parabolic.FlattenedJacquetQuotientProof`
- `Langlands.Representation.Parabolic.FlattenedJacquetQuotientStatement`
- `Langlands.Representation.Parabolic.FlattenedRefinementModulusCalculation`
- `Langlands.Representation.Parabolic.GeometricPrerequisitesStatement`
- `Langlands.Representation.Parabolic.HeadTailProductInduction`
- `Langlands.Representation.Parabolic.InductionFactorMatchingProof`
- `Langlands.Representation.Parabolic.InductionFactorMatchingStatement`
- `Langlands.Representation.Parabolic.JacquetFiniteGenerationProof`
- `Langlands.Representation.Parabolic.JacquetFiniteGenerationStatement`
- `Langlands.Representation.Parabolic.LeviBridges`
- `Langlands.Representation.Parabolic.LeviInflationAdmissibilityProof`
- `Langlands.Representation.Parabolic.NormalizedAdmissibilityProof`
- `Langlands.Representation.Parabolic.NormalizedInductionStatement`
- `Langlands.Representation.Parabolic.NormalizedJacquetAdmissibilityProof`
- `Langlands.Representation.Parabolic.NormalizedJacquetExactnessProof`
- `Langlands.Representation.Parabolic.NormalizedJacquetStatement`
- `Langlands.Representation.Parabolic.OrderedProductRegroupingEquivalence`
- `Langlands.Representation.Parabolic.OrderedProductRegroupingProof`
- `Langlands.Representation.Parabolic.OrderedProductRegroupingStatement`
- `Langlands.Representation.Parabolic.OrderedRefinementInduction`
- `Langlands.Representation.Parabolic.OrderedRefinementTensorInduction`
- `Langlands.Representation.Parabolic.QuotientCompactProof`
- `Langlands.Representation.Parabolic.RefinedInductionAdmissibility`
- `Langlands.Representation.Parabolic.RefinedInductionTensorMap`
- `Langlands.Representation.Parabolic.RefinedInductionTensorNormalization`
- `Langlands.Representation.Parabolic.RefinedInductionTensorProof`
- `Langlands.Representation.Parabolic.RefinedInductionTensorStatement`
- `Langlands.Representation.Parabolic.RefinedInnerInductionObjects`
- `Langlands.Representation.Parabolic.RefinementCharacter`
- `Langlands.Representation.Parabolic.RefinementComposition`
- `Langlands.Representation.Parabolic.RefinementCoordinatesNormalizationProof`
- `Langlands.Representation.Parabolic.RefinementCoordinatesNormalizationStatement`
- `Langlands.Representation.Parabolic.RefinementInductionTransitivityProof`
- `Langlands.Representation.Parabolic.RefinementPreimage`
- `Langlands.Representation.Parabolic.RefinementTransitivityStatement`
- `Langlands.Representation.Parabolic.RegroupingFactorEquivalences`
- `Langlands.Representation.Parabolic.ThreeBlockCarrierComparison`
- `Langlands.Representation.Parabolic.ThreeBlockInductionAssociativityStatement`
- `Langlands.Representation.Parabolic.ThreeBlockRefinementGeometry`
- `Langlands.Representation.Parabolic.ThreeBlockRegroupingAssembly`
- `Langlands.Representation.Parabolic.ThreeBlockUniverseReduction`
- `Langlands.Representation.Parabolic.UnipotentFiniteContainment`
- `Langlands.Representation.RankinSelberg.AnalyticStatement`
- `Langlands.Representation.RankinSelberg.FunctionalEquationStatement`
- `Langlands.Representation.RankinSelberg.GeneralLinearUnimodularity`
- `Langlands.Representation.RankinSelberg.HaarSymmetriesProof`
- `Langlands.Representation.RankinSelberg.HaarSymmetriesStatement`
- `Langlands.Representation.RankinSelberg.LastRowCompactOrbitProof`
- `Langlands.Representation.RankinSelberg.LastRowCompactOrbitStatement`
- `Langlands.Representation.RankinSelberg.Measures`
- `Langlands.Representation.RankinSelberg.QuotientIntegrals`
- `Langlands.Representation.RankinSelberg.RationalContinuation`
- `Langlands.Representation.RankinSelberg.RationalZeta`
- `Langlands.Representation.RankinSelberg.UnimodularityStatement`
- `Langlands.Representation.RankinSelberg.UnipotentUnimodularity`
- `Langlands.Representation.RankinSelberg.ZeroRowLastRowCutoffProof`
- `Langlands.Representation.RankinSelberg.ZeroRowLastRowCutoffStatement`
- `Langlands.Representation.Schur.CountableDimensionProof`
- `Langlands.Representation.Schur.CountableDimensionStatement`
- `Langlands.Representation.Shahidi.Geometry`
- `Langlands.Representation.Shahidi.Induction`
- `Langlands.Representation.Shahidi.TwoBlocks`
- `Langlands.Representation.Smooth.Admissibility.CofinalProof`
- `Langlands.Representation.Smooth.Admissibility.CofinalStatement`
- `Langlands.Representation.Smooth.Admissibility.EmbeddingProof`
- `Langlands.Representation.Smooth.Admissibility.EmbeddingStatement`
- `Langlands.Representation.Smooth.Admissibility.EquivalenceProof`
- `Langlands.Representation.Smooth.Admissibility.EquivalenceStatement`
- `Langlands.Representation.Smooth.Admissibility.Extension`
- `Langlands.Representation.Smooth.ConstituentSupport`
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
- `Langlands.Representation.Smooth.IrreducibleCompositionFactors`
- `Langlands.Representation.Smooth.IrreducibleGrothendieckProof`
- `Langlands.Representation.Smooth.IrreducibleGrothendieckStatement`
- `Langlands.Representation.Smooth.IrreducibleRealization`
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
- `Langlands.Representation.Tensor.CoinvariantReflection`
- `Langlands.Representation.Tensor.FactorMatchingProof`
- `Langlands.Representation.Tensor.FactorMatchingStatement`
- `Langlands.Representation.Tensor.Filtration`
- `Langlands.Representation.Tensor.Finite`
- `Langlands.Representation.Tensor.FiniteEquivalences`
- `Langlands.Representation.Tensor.FiniteProperties`
- `Langlands.Representation.Tensor.FiniteRegrouping`
- `Langlands.Representation.Tensor.GLRefinement`
- `Langlands.Representation.Tensor.OneFactor`
- `Langlands.Representation.Twist.AdmissibilityProof`
- `Langlands.Representation.Twist.AdmissibilityStatement`
- `Langlands.Representation.Twist.AlgebraProof`
- `Langlands.Representation.Twist.AlgebraStatement`
- `Langlands.Representation.Twist.ContinuousCharacterProof`
- `Langlands.Representation.Twist.ContinuousCharacterStatement`
- `Langlands.Representation.Twist.Definitions`
- `Langlands.Representation.Twist.RealPower`
- `Langlands.Representation.Twist.SmoothProof`
- `Langlands.Representation.Twist.SmoothStatement`
- `Langlands.Representation.Twist.SubquotientDefinitions`
- `Langlands.Representation.Twist.SubquotientProof`
- `Langlands.Representation.Twist.SubquotientStatement`
- `Langlands.Representation.Unitary.Basic`
- `Langlands.Representation.Unramified.Eigenvalues`
- `Langlands.Representation.Unramified.HeckeOperators`
- `Langlands.Representation.Unramified.PrincipalSeries`
- `Langlands.Representation.Unramified.SphericalClassificationStatement`
- `Langlands.Representation.Unramified.SphericalConstituentExistenceProof`
- `Langlands.Representation.Whittaker.Algebraic`
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
- `Langlands.Representation.Whittaker.CoefficientDistribution`
- `Langlands.Representation.Whittaker.CompatibleMonomialFixedProof`
- `Langlands.Representation.Whittaker.CompatibleMonomialFixedStatement`
- `Langlands.Representation.Whittaker.CompatibleTorus`
- `Langlands.Representation.Whittaker.Distribution`
- `Langlands.Representation.Whittaker.DistributionInvarianceProof`
- `Langlands.Representation.Whittaker.DistributionInvarianceStatement`
- `Langlands.Representation.Whittaker.DualTransform`
- `Langlands.Representation.Whittaker.GeneralLinear`
- `Langlands.Representation.Whittaker.GeneralizedCoefficient`
- `Langlands.Representation.Whittaker.GeneralizedCoefficientDescent`
- `Langlands.Representation.Whittaker.GeneralizedCoefficientKernelProof`
- `Langlands.Representation.Whittaker.GeneralizedCoefficientKernelStatement`
- `Langlands.Representation.Whittaker.GeneralizedCoefficientSeparation`
- `Langlands.Representation.Whittaker.GenericDualTransport`
- `Langlands.Representation.Whittaker.Iwasawa`
- `Langlands.Representation.Whittaker.MultiplicityOneProof`
- `Langlands.Representation.Whittaker.MultiplicityOneStatement`
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

## Complete external import frontier

- `Lean.Elab.Tactic.Omega`
- `Mathlib.Algebra.Algebra.Bilinear`
- `Mathlib.Algebra.Algebra.NonUnitalHom`
- `Mathlib.Algebra.Algebra.NonUnitalSubalgebra`
- `Mathlib.Algebra.Algebra.Subalgebra.Lattice`
- `Mathlib.Algebra.BigOperators.Fin`
- `Mathlib.Algebra.BigOperators.Finprod`
- `Mathlib.Algebra.BigOperators.Group.Finset.Basic`
- `Mathlib.Algebra.BigOperators.Group.List.Basic`
- `Mathlib.Algebra.BigOperators.GroupWithZero.Action`
- `Mathlib.Algebra.BigOperators.Pi`
- `Mathlib.Algebra.BigOperators.Ring.Finset`
- `Mathlib.Algebra.Category.ModuleCat.Basic`
- `Mathlib.Algebra.CharP.Basic`
- `Mathlib.Algebra.DirectSum.Module`
- `Mathlib.Algebra.Exact.Basic`
- `Mathlib.Algebra.Field.Subfield.Basic`
- `Mathlib.Algebra.Group.Action.Hom`
- `Mathlib.Algebra.Group.Action.Opposite`
- `Mathlib.Algebra.Group.Equiv.TypeTags`
- `Mathlib.Algebra.Group.Hom.Instances`
- `Mathlib.Algebra.Group.Pi.Lemmas`
- `Mathlib.Algebra.Group.Subgroup.Ker`
- `Mathlib.Algebra.Group.Subgroup.Pointwise`
- `Mathlib.Algebra.Group.Submonoid.Basic`
- `Mathlib.Algebra.Group.TypeTags.Finite`
- `Mathlib.Algebra.Group.TypeTags.Hom`
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
- `Mathlib.Analysis.Matrix.MeasurableSpace`
- `Mathlib.Analysis.Matrix.Normed`
- `Mathlib.Analysis.MeanInequalitiesPow`
- `Mathlib.Analysis.Normed.Module.FiniteDimension`
- `Mathlib.Analysis.Normed.Operator.BoundedLinearMaps`
- `Mathlib.Analysis.Normed.Unbundled.SpectralNorm`
- `Mathlib.Analysis.Real.Sqrt`
- `Mathlib.Analysis.SpecialFunctions.Complex.Circle`
- `Mathlib.Analysis.SpecialFunctions.Pow.Complex`
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
- `Mathlib.CategoryTheory.Products.Basic`
- `Mathlib.CategoryTheory.Skeletal`
- `Mathlib.CategoryTheory.Whiskering`
- `Mathlib.Combinatorics.Enumerative.Composition`
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
- `Mathlib.LinearAlgebra.AnnihilatingPolynomial`
- `Mathlib.LinearAlgebra.Basis.VectorSpace`
- `Mathlib.LinearAlgebra.BilinearForm.Properties`
- `Mathlib.LinearAlgebra.Charpoly.Basic`
- `Mathlib.LinearAlgebra.Charpoly.ToMatrix`
- `Mathlib.LinearAlgebra.Determinant`
- `Mathlib.LinearAlgebra.Dimension.Basic`
- `Mathlib.LinearAlgebra.Dimension.Constructions`
- `Mathlib.LinearAlgebra.Dimension.StrongRankCondition`
- `Mathlib.LinearAlgebra.DirectSum.Finite`
- `Mathlib.LinearAlgebra.Dual.Defs`
- `Mathlib.LinearAlgebra.Dual.Lemmas`
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
- `Mathlib.LinearAlgebra.Matrix.Rank`
- `Mathlib.LinearAlgebra.Matrix.Reindex`
- `Mathlib.LinearAlgebra.Matrix.SchurComplement`
- `Mathlib.LinearAlgebra.Matrix.Transvection`
- `Mathlib.LinearAlgebra.PiTensorProduct.Basic`
- `Mathlib.LinearAlgebra.PiTensorProduct.Basis`
- `Mathlib.LinearAlgebra.PiTensorProduct.Finite`
- `Mathlib.LinearAlgebra.PiTensorProduct.Generators`
- `Mathlib.LinearAlgebra.Projection`
- `Mathlib.LinearAlgebra.Quotient.Basic`
- `Mathlib.LinearAlgebra.Semisimple`
- `Mathlib.LinearAlgebra.TensorProduct.Basis`
- `Mathlib.LinearAlgebra.TensorProduct.RightExactness`
- `Mathlib.LinearAlgebra.Trace`
- `Mathlib.Logic.Equiv.Fin.Basic`
- `Mathlib.MeasureTheory.Constructions.Pi`
- `Mathlib.MeasureTheory.Function.LocallyIntegrable`
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
- `Mathlib.RingTheory.Flat.Basic`
- `Mathlib.RingTheory.FractionalIdeal.Operations`
- `Mathlib.RingTheory.Ideal.Quotient.Basic`
- `Mathlib.RingTheory.Ideal.Quotient.Operations`
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
- `Mathlib.RingTheory.Trace.Basic`
- `Mathlib.RingTheory.Valuation.Extension`
- `Mathlib.RingTheory.Valuation.Integral`
- `Mathlib.RingTheory.Valuation.LocalSubring`
- `Mathlib.RingTheory.Valuation.RamificationGroup`
- `Mathlib.Tactic`
- `Mathlib.Tactic.Group`
- `Mathlib.Tactic.Linarith`
- `Mathlib.Tactic.NoncommRing`
- `Mathlib.Tactic.NormNum`
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
- `Mathlib.Topology.Connected.TotallyDisconnected`
- `Mathlib.Topology.ContinuousMap.CompactlySupported`
- `Mathlib.Topology.Homeomorph.Defs`
- `Mathlib.Topology.Homeomorph.Lemmas`
- `Mathlib.Topology.Homeomorph.Quotient`
- `Mathlib.Topology.Instances.Int`
- `Mathlib.Topology.Instances.Matrix`
- `Mathlib.Topology.Instances.NNReal.Lemmas`
- `Mathlib.Topology.LocallyClosed`
- `Mathlib.Topology.LocallyConstant.Algebra`
- `Mathlib.Topology.LocallyConstant.Basic`
- `Mathlib.Topology.MetricSpace.Ultra.TotallySeparated`
- `Mathlib.Topology.Order.Compact`
- `Mathlib.Topology.Separation.Profinite`
- `Mathlib.Topology.UrysohnsLemma`
