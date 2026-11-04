# Supplied special-head embeddings at consecutive cuts

Author: Worker 357.

This internal construction returns an actual injective intertwiner from a
supplied special head to the ordered product of supplied special heads of its
two consecutive pieces. It assembles published individual-head, induction,
finite-length and strong-socle results. No new assertion is transcribed from
original literature.

## Interface and conventions

The declaration is
`Langlands.Classification.SegmentHeadCut.headCutEmbedding`.
Fix arbitrary `{p : ℕ} [Fact p.Prime]`, an actual
`F : PadicField.{uF} p`, and supplied `T : F.TopologicalData`.
The construction installs exactly `T.topology`.

Let `ρ : CuspidalDatum.{uV,uF} T`, write `r = ρ.rank`, and let
`a,b : ℕ` with `ha : 0 < a` and `hb : 0 < b`.
The three smooth representations and their supplied relations are:

| Representation | Group rank | Supplied relation |
| --- | --- | --- |
| `π` | `(a+b)*r` | `T.IsSegmentHead ⟨ρ,a+b,by omega⟩ π` |
| `π₁` | `a*r` | `T.IsSegmentHead ⟨ρ.twist (b : ℝ),a,ha⟩ π₁` |
| `π₂` | `b*r` | `T.IsSegmentHead ⟨ρ,b,hb⟩ π₂` |

The caller also supplies an actual
`A : SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := r)` and
`hA : ρ.IsRepresentedBy A`. With

```text
P = T.binaryNormalizedProductFunctor (a*r) (b*r)
C = generalLinearRankCast T (Nat.add_mul a b r).symm
```

the returned value has type

```text
{j : π.representation.IntertwiningMap (C.obj (P.obj (π₁,π₂))).representation //
  Function.Injective j}.
```

`P` uses the upper block parabolic, normalized covariance and right
translation of the published construction. The first factor is the upper,
shifted piece; the second is the lower, original-base piece. `C` transports
rank `a*r+b*r` to `(a+b)*r` using that literal equality. The output is a
chosen equivariant complex-linear map retaining injectivity. No preferred
choice or naturality law for this selected map is asserted.

The base-carrier universe `uV` is independent of `uF`. `A` has carrier in
`Type uV`; all three heads and every induced carrier used in the construction
are in `Type (max uF uV)`. There is no carrier resizing, finite vector-space
dimension assumption, or change of topological realization.

`IsSegmentHead` is the strong irreducible quotient relation for increasing
segment induction, with uniqueness of actual quotient kernels. The proof
identifies that supplied head with the strong socle of decreasing induction
by a separately proved individual-segment result. It does not replace it by
the socle of increasing induction.

## Implemented construction

Form the actual supercuspidal object `A₁` by twisting `A` with
`T.determinantPowerCharacter r (b : ℝ)`. The published
`SupercuspidalRep.twist` uses the open-kernel and determinant-kernel
conditions supplied by `T`. Rewriting `hA` proves that `A₁` represents
`ρ.twist (b : ℝ)`: the class twist is then definitionally the class of
this actual twisted object. Its smooth object agrees with
`T.segmentFactor A.obj (b : ℝ)`.

Apply `IsSegmentHead.decreasingSocleEmbedding` to `hπ₁,A₁` and to `hπ₂,A`.
These give actual injective intertwiners into

```text
D₁ = T.segmentInducedDown (T.segmentFactor A.obj (b : ℝ)) a ρ.rank_pos
D₂ = T.segmentInducedDown A.obj b ρ.rank_pos.
```

Convert these to smooth morphisms `i₁,i₂`.
`T.binaryProductMap_injective` proves actual injectivity of
`I = P.map (i₁,i₂)`. The published consecutive-cut isomorphism has direction

```text
e : T.segmentInducedDown A.obj (a+b) ρ.rank_pos ≅ C.obj (P.obj (D₁,D₂)).
```

Thus `C.map I ≫ e.inv` injects `C.obj (P.obj (π₁,π₂))` into the long
decreasing induction. The private `rankCast_injective` eliminates the rank
equality; `comp_injective` uses literal composition of smooth intertwiners.
The inverse isomorphism is injective by
`SmoothRep.hom_hom_injective e.symm`.

The two shorter heads are irreducible by
`IsSegmentHead.isIrreducibleSocle_down`, so their carriers are nontrivial
simple modules over their actual group algebras.
`ProductVanishing.nontrivial_binary` makes `P.obj (π₁,π₂)` nontrivial.
The private `binaryFiniteLength` rewrites the positive-rank binary product
as normalized induction of the binary block shape and applies
`irreducibleProductFiniteLength` to its two irreducible factors.
Both block ranks are positive because `a,b,r` are positive.
The private `rankCast_nontrivial` and `rankCast_finiteLength` retain these
facts by eliminating the equality of ranks.

Finally `hπ.isIrreducibleSocle_down A hA` supplies the long decreasing
strong-socle relation. Apply
`IsIrreducibleSocle.finiteLengthSubobjectEmbedding` to this ambient
representation, the nonzero finite-length product, and the injection
`C.map I ≫ e.inv`. Its result is exactly the promised `π`-to-product map.
All three carriers in this application lie in the same maximum universe,
as required by the general strong-socle relation.

The five private lemmas are the binary finite-length specialization, the
three equality-transport facts, and composition of injective morphisms.
They are grouped with the constructor as one focused unit.

## Published inputs and proof-dependency audit

The audit uses Library `8a1c71c3b7e45f52546ca1d740fc0b623ffb6299`.
Every inherited project Lean file and its nonempty Markdown pair in the
recursive closure matches that published tree byte for byte. Only this
module's pair is new. The complete inventory follows below: 781 project
modules including this root and 254 distinct external imports at the project
boundary. The latter is a frontier count, not a transitive Mathlib inventory.

The used proof bodies have these mathematical roles:

- `SegmentHeadDecreasingSocle` compares any supplied strong head with the
  individually constructed special representation through their canonical
  heads and transports its decreasing strong socle. Its
  `SegmentSpecialConstituentExistenceProof` input obtains strong endpoints
  from a common-image multiplicity-one argument, using actual
  geometric-lemma cuspidal Jacquet counts, exactness, quotient/subobject
  detection, an associated-induction map and admissibility. These are
  individual-segment constructions and counts, with no full segment
  Jacquet formula.
- `SegmentDownCut` proves the consecutive coordinate equality for a binary
  outer shape refined by two uniform shapes. Proved ordered regrouping
  and generic binary/rank object equalities give the actual cut, and actual
  determinant-twist composition identifies its decreasing subfamilies.
  It works for arbitrary smooth bases and uses no head or derivative formula.
- `Induction.BinaryProductSubquotients.binaryProductMap_injective` uses
  tensor injectivity and induced-map injectivity at positive ranks;
  its zero-rank cases use tensor models. This constructor uses the
  positive-rank case, without a segment-specific product structure theorem.
- `IrreducibleProductFiniteLengthProof` embeds an arbitrary irreducible-factor
  product in a product of cuspidal embeddings, regroups it as cuspidal
  induction and transfers finite group-algebra length along the injection.
  The lower length proof uses a finite Jacquet detecting family and actual
  associated/nonassociated geometric filtrations, without classification.
- `ProductVanishing.nontrivial_binary` uses a nonzero slot subrepresentation
  of normalized induction at positive ranks. The theorem's zero-rank cases
  use nonzero complex tensor products. Only product nonvanishing is used.
- `ArtinianSocleEmbedding` extracts an atom of the nonzero source's
  group-algebra submodule lattice using Artinianity. The ambient injection
  produces an irreducible embedding. Strong-socle image uniqueness and
  canonical-socle equivalences identify this atom with the supplied socle;
  its subtype inclusion gives the map. Finite group-algebra length supplies
  Artinianity. No ambient Artinianity is assumed.
- `Derivative.Iteration.generalLinearRankCast` is equality transport between
  smooth categories at equal ranks. Only this transport is used from
  derivative iteration.

The derivative/mirabolic modules in the full closure are exactly
`Derivative.Iteration`, `Derivative.MirabolicMinus`,
`Derivative.MirabolicCharacter`, `Derivative.ProductVanishing`, and
`Mirabolic.MixedProducts`. They supply general constructions, rank transport
and nonvanishing; no segment derivative result is used. General analytic
predicates and `TemperedSupportStatement`/`TemperedInductionStatement` also
occur as definitions. They supply no theorem conclusion here.

A scan of code with comments and string literals removed checked excluded
task identifiers and excluded classification, product, derivative and
Jacquet declarations. It found no matches, missing inherited pairs, proof
holes, new axioms or prohibited execution syntax. This inventory was
combined with examination of the used proof bodies and the published
individual-head and generic length routes described above. This is an
author dependency audit, not independent semantic acceptance, and does not
claim that all 781 inherited files were newly read line by line.

## Operator rulings and retained exclusions

The complete trusted operator responses governing the host's dependency
conditions were read at:

- `/home/taskhub/pilot/correspondence/bd71b9185aab5d6eafffb7891bd3a3ca.md`;
- `/home/taskhub/pilot/correspondence/0edda6122ce65ed7ac51603c37473920.md`;
- `/home/taskhub/pilot/correspondence/30144f6f9b59540b88b6d4c1517892d9.md`;
- `/home/taskhub/pilot/correspondence/ed80148e21e7523abfc048f455e98eb0.md`;
- `/home/taskhub/pilot/correspondence/2b33898bdd0a5ff1b9031be5155a06f0.md`;
- `/home/taskhub/pilot/correspondence/ca18fd5005bf5e12a3f7cade18dca865.md`.

The first permits a fully proved general derivative route; the second extends
permitted general infrastructure while preserving exclusions. The third
permits exactly the specified independently proved support bound as a later
host input. The fourth confines `core_mid` and its simple-factor consequence
to that support proof's length-two base. The last two permit adjacent
supercuspidal reducibility only for that support proof. None of that support
bound, `core_mid`, or restricted reducibility occurs in this closure.

The closure preserves independence from Ze80 3.5/9.6 and their successors;
the excluded segment, head, socle, full-Jacquet and classification conclusions;
and the segment-socle part of `8e5b4563-0365-41c7-b134-70f2a0b36292`.
It uses no `SegmentHeadSupportStep`, `SegmentHeadJacquetReduction`,
`TwoSupercuspidalProductStructureProof`, or `UniverseLiftPadic`.
It imports neither direction of the full special-head product criterion nor
any downstream uniqueness, exhaustion, ordered-head, quotient-coverage,
tempered, square-integrable or regular classification proof excluded by the
host contract.

The provenance is internal assembly of published constructions and proofs.
This contribution establishes only the displayed actual cut embedding.
It asserts no derivative nonvanishing, derivative identification, derivative
irreducibility, multiplicity formula, or full product irreducibility equivalence.

## Complete project import inventory

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
Langlands.Group.GL.BlockUnipotent
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
Langlands.Group.GL.InverseTransposeIwahoriProof
Langlands.Group.GL.InverseTransposeIwahoriStatement
Langlands.Group.GL.Maps
Langlands.Group.GL.Mirabolic
Langlands.Group.GL.MirabolicMixedProductSubgroups
Langlands.Group.GL.MirabolicOppositeIntersection
Langlands.Group.GL.MirabolicProjection
Langlands.Group.GL.MirabolicRadical
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
Langlands.Group.GL.RankReindex
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
Langlands.HarmonicAnalysis.FiniteProductMeasureScaling
Langlands.HarmonicAnalysis.HaarConjugacy
Langlands.HarmonicAnalysis.PadicHaarScalingStatement
Langlands.HarmonicAnalysis.PadicRectangularHaarScalingProof
Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof
Langlands.HarmonicAnalysis.TriangularTranslationProof
Langlands.HarmonicAnalysis.TriangularTranslationStatement
Langlands.LocalFactor.Euler.Definitions
Langlands.LocalFactor.RankOne
Langlands.LocalField.Canonical
Langlands.LocalField.Definitions
Langlands.LocalField.Normalization.Definitions
Langlands.LocalField.Normalization.Proof
Langlands.LocalField.Normalization.Statement
Langlands.LocalField.Topology
Langlands.LocalField.Uniformizer
Langlands.Representation.Category.Abelian
Langlands.Representation.Category.Basic
Langlands.Representation.Category.ClassInvariants
Langlands.Representation.Category.ConstituentDichotomy
Langlands.Representation.Category.ConstituentDichotomyStatement
Langlands.Representation.Category.Contragredient
Langlands.Representation.Category.FiniteIndexRestriction
Langlands.Representation.Category.FiniteIndexSemisimplicity
Langlands.Representation.Category.FiniteIndexSemisimplicityStatement
Langlands.Representation.Category.RestrictionSubquotients
Langlands.Representation.Category.Subquotients
Langlands.Representation.Category.Twist
Langlands.Representation.Category.UniverseLift
Langlands.Representation.Classification.ArtinianSocleEmbedding
Langlands.Representation.Classification.CanonicalConstituents
Langlands.Representation.Classification.CommonImageMultiplicityOneProof
Langlands.Representation.Classification.CommonImageMultiplicityOneStatement
Langlands.Representation.Classification.ConstituentRelations
Langlands.Representation.Classification.Cosocle
Langlands.Representation.Classification.CuspidalIntegralTwistFreenessProof
Langlands.Representation.Classification.CuspidalIntegralTwistFreenessStatement
Langlands.Representation.Classification.CuspidalJacquetFunctorExactnessProof
Langlands.Representation.Classification.CuspidalJacquetFunctorExactnessStatement
Langlands.Representation.Classification.CuspidalJacquetFunctors
Langlands.Representation.Classification.CuspidalJacquetMultiplicityProof
Langlands.Representation.Classification.CuspidalJacquetMultiplicityStatement
Langlands.Representation.Classification.Essential
Langlands.Representation.Classification.HeadQuotientCriterionProof
Langlands.Representation.Classification.HeadQuotientCriterionStatement
Langlands.Representation.Classification.IrreducibleProductEmbedding
Langlands.Representation.Classification.IrreducibleProductEmbeddingStatement
Langlands.Representation.Classification.IrreducibleProductFiniteLengthProof
Langlands.Representation.Classification.JuxtaposedRefinementTools
Langlands.Representation.Classification.LanglandsData
Langlands.Representation.Classification.MultiplicityOneConstituentProof
Langlands.Representation.Classification.MultiplicityOneConstituentStatement
Langlands.Representation.Classification.NormalizedProductFiniteLengthStatement
Langlands.Representation.Classification.OppositeCuspidalJacquetFiltrationProof
Langlands.Representation.Classification.OppositeCuspidalJacquetFiltrationStatement
Langlands.Representation.Classification.OppositeJacquetQuotientDetectionProof
Langlands.Representation.Classification.OppositeJacquetQuotientDetectionStatement
Langlands.Representation.Classification.OppositeJacquetReciprocity
Langlands.Representation.Classification.OppositeSupportJacquetAdapter
Langlands.Representation.Classification.RelativeGenericityStatement
Langlands.Representation.Classification.RelativeJacquetMultiplicityStatement
Langlands.Representation.Classification.RelativeRegularComparisonStatement
Langlands.Representation.Classification.SegmentConstituentStatement
Langlands.Representation.Classification.SegmentDownCut
Langlands.Representation.Classification.SegmentHeadCutEmbedding
Langlands.Representation.Classification.SegmentHeadDecreasingSocle
Langlands.Representation.Classification.SegmentInductionAdmissibilityProof
Langlands.Representation.Classification.SegmentInductionAdmissibilityStatement
Langlands.Representation.Classification.SegmentJacquetMultiplicityProof
Langlands.Representation.Classification.SegmentJacquetMultiplicityStatement
Langlands.Representation.Classification.SegmentJacquetReversal
Langlands.Representation.Classification.SegmentProductSplit
Langlands.Representation.Classification.SegmentSpecialConstituentExistenceProof
Langlands.Representation.Classification.SegmentTensorReversalProof
Langlands.Representation.Classification.SegmentTensorReversalStatement
Langlands.Representation.Classification.SegmentTensorStabilizerProof
Langlands.Representation.Classification.SegmentTensorStabilizerStatement
Langlands.Representation.Classification.Segments
Langlands.Representation.Classification.Supercuspidal
Langlands.Representation.Classification.SupercuspidalContragredientAux
Langlands.Representation.Classification.SupercuspidalContragredientStatement
Langlands.Representation.Classification.SupercuspidalSupport
Langlands.Representation.Classification.SupercuspidalTwist
Langlands.Representation.Classification.Tempered
Langlands.Representation.Classification.TemperedInductionStatement
Langlands.Representation.Classification.TemperedSupportStatement
Langlands.Representation.Classification.UpperCuspidalJacquetMultiplicityProof
Langlands.Representation.Classification.UpperCuspidalJacquetMultiplicityStatement
Langlands.Representation.Classification.UpperJacquetSubrepresentationDetectionProof
Langlands.Representation.Classification.UpperJacquetSubrepresentationDetectionStatement
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
Langlands.Representation.CompactCoefficient.SelectedAssembly
Langlands.Representation.CompactCoefficient.SelectedBlock
Langlands.Representation.CompactCoefficient.SelectedConjugation
Langlands.Representation.CompactCoefficient.SelectedCoverage
Langlands.Representation.CompactCoefficient.SelectedProjector
Langlands.Representation.CompactCoefficient.SemisimplicityProof
Langlands.Representation.CompactCoefficient.SemisimplicityStatement
Langlands.Representation.CompactCoefficient.TotalCompactness
Langlands.Representation.CompactCoefficient.TotalProjector
Langlands.Representation.Conductor.Congruence
Langlands.Representation.Conductor.Definitions
Langlands.Representation.Conductor.PrincipalCongruence
Langlands.Representation.Conductor.PrincipalCongruenceBasisProof
Langlands.Representation.Conductor.PrincipalCongruenceBasisStatement
Langlands.Representation.CuspidalSupport.AssociatedAssembly
Langlands.Representation.CuspidalSupport.AssociatedConditional
Langlands.Representation.CuspidalSupport.AssociatedGeometricPieceVanishingProof
Langlands.Representation.CuspidalSupport.AssociatedGeometricPiecesEquivalenceProof
Langlands.Representation.CuspidalSupport.AssociatedGeometricPiecesProof
Langlands.Representation.CuspidalSupport.AssociatedGeometricPiecesStatement
Langlands.Representation.CuspidalSupport.AssociatedProof
Langlands.Representation.CuspidalSupport.AssociatedRankZero
Langlands.Representation.CuspidalSupport.AssociationForwardHomProof
Langlands.Representation.CuspidalSupport.AssociationForwardHomSupport
Langlands.Representation.CuspidalSupport.AssociationForwardStatement
Langlands.Representation.CuspidalSupport.AssociationLawsProof
Langlands.Representation.CuspidalSupport.AssociationLawsStatement
Langlands.Representation.CuspidalSupport.AssociationReduction
Langlands.Representation.CuspidalSupport.BlockMap
Langlands.Representation.CuspidalSupport.BlockPermutation
Langlands.Representation.CuspidalSupport.BlockWeylTransport
Langlands.Representation.CuspidalSupport.CentralShift
Langlands.Representation.CuspidalSupport.CompactCoefficientFinitenessProof
Langlands.Representation.CuspidalSupport.CompactCoefficientFinitenessReduction
Langlands.Representation.CuspidalSupport.CompactCoefficientFinitenessStatement
Langlands.Representation.CuspidalSupport.ConstituentComplement
Langlands.Representation.CuspidalSupport.ConstituentComplementStatement
Langlands.Representation.CuspidalSupport.ConstituentFiniteTypes
Langlands.Representation.CuspidalSupport.ConstituentInduction
Langlands.Representation.CuspidalSupport.ConstituentInductionStatement
Langlands.Representation.CuspidalSupport.ConstituentProof
Langlands.Representation.CuspidalSupport.ConstituentRankZero
Langlands.Representation.CuspidalSupport.ConstituentSemisimple
Langlands.Representation.CuspidalSupport.ConstituentSemisimpleStatement
Langlands.Representation.CuspidalSupport.CuspidalBlockIsolationProof
Langlands.Representation.CuspidalSupport.CuspidalBlockIsolationStatement
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
Langlands.Representation.CuspidalSupport.DeterminantUnitFiniteRestriction
Langlands.Representation.CuspidalSupport.DeterminantUnitStructureProof
Langlands.Representation.CuspidalSupport.DeterminantUnitStructureStatement
Langlands.Representation.CuspidalSupport.DistinctTensorStabilizerProof
Langlands.Representation.CuspidalSupport.DistinctTensorStabilizerStatement
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
Langlands.Representation.CuspidalSupport.QuasicuspidalLeviAdmissibilityProof
Langlands.Representation.CuspidalSupport.QuasicuspidalPrerequisitesStatement
Langlands.Representation.CuspidalSupport.QuasicuspidalStructureStatement
Langlands.Representation.CuspidalSupport.StandardJacquetComparisonProof
Langlands.Representation.CuspidalSupport.TotalConjugatingCountProof
Langlands.Representation.CuspidalSupport.TotalConjugatingCountStatement
Langlands.Representation.CuspidalSupport.ZeroRankEmbeddingProof
Langlands.Representation.Derivative.Iteration
Langlands.Representation.Derivative.MirabolicCharacter
Langlands.Representation.Derivative.MirabolicMinus
Langlands.Representation.Derivative.ProductVanishing
Langlands.Representation.Dual.Definitions
Langlands.Representation.Exponents.Central
Langlands.Representation.Exponents.ComplexTwistFamilies
Langlands.Representation.Exponents.DualJacquet
Langlands.Representation.Exponents.DualJacquetStatement
Langlands.Representation.Exponents.Jacquet
Langlands.Representation.Exponents.NilpotenceIndex
Langlands.Representation.Exponents.ParabolicPair
Langlands.Representation.Exponents.RealTwistFamilies
Langlands.Representation.Exponents.SupportedRegularMultiplicityBranchObstructionStatement
Langlands.Representation.Exponents.UnitaryDualJacquetSupportAdapters
Langlands.Representation.Exponents.WeylBranchPiecesStatement
Langlands.Representation.Exponents.WeylBranchPiecesSubquotient
Langlands.Representation.Filtration.CoinvariantVanishingStatement
Langlands.Representation.Filtration.Definitions
Langlands.Representation.Filtration.FiniteFamilyMultiplicityProof
Langlands.Representation.Filtration.FiniteFamilyMultiplicityStatement
Langlands.Representation.Filtration.GradedRefinementProof
Langlands.Representation.Filtration.GradedRefinementStatement
Langlands.Representation.Filtration.IntervalLiftProof
Langlands.Representation.Filtration.IntervalLiftStatement
Langlands.Representation.Filtration.IrreducibleMultiplicityProof
Langlands.Representation.Filtration.IrreducibleMultiplicityStatement
Langlands.Representation.Filtration.IsoTransport
Langlands.Representation.Filtration.JordanHolderComparisonProof
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
Langlands.Representation.Filtration.SimpleMapMultiplicityDetectionProof
Langlands.Representation.Filtration.SimpleMapMultiplicityDetectionStatement
Langlands.Representation.Filtration.SubquotientAlgebraProof
Langlands.Representation.Filtration.SubquotientAlgebraStatement
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
Langlands.Representation.Geometric.CoarseLeviReversal
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
Langlands.Representation.Hecke.DoubleCoset
Langlands.Representation.Hecke.DoubleCosetSandwich
Langlands.Representation.Hecke.IntegratedAction
Langlands.Representation.Hecke.IntegratedConvolution
Langlands.Representation.Hecke.NormalizedIndicator
Langlands.Representation.Hecke.TestFunction
Langlands.Representation.Induction.BinaryProduct
Langlands.Representation.Induction.BinaryProductSubquotients
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
Langlands.Representation.Induction.HeterogeneousConstruction
Langlands.Representation.Induction.HeterogeneousPairs
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
Langlands.Representation.Jacquet.CanonicalLiftGroupTransportProof
Langlands.Representation.Jacquet.CanonicalLiftGroupTransportStatement
Langlands.Representation.Jacquet.CanonicalLiftIntertwinerNaturalityProof
Langlands.Representation.Jacquet.CanonicalLiftIntertwinerNaturalityStatement
Langlands.Representation.Jacquet.CanonicalLiftStatement
Langlands.Representation.Jacquet.CharacterTwistEquiv
Langlands.Representation.Jacquet.Coinvariants
Langlands.Representation.Jacquet.CompactCompressionStableDualityProof
Langlands.Representation.Jacquet.CompactCompressionStableDualityStatement
Langlands.Representation.Jacquet.CompressionStabilizationProof
Langlands.Representation.Jacquet.CompressionStabilizationStatement
Langlands.Representation.Jacquet.ExactProof
Langlands.Representation.Jacquet.ExactStatement
Langlands.Representation.Jacquet.Localization
Langlands.Representation.Jacquet.Normalized
Langlands.Representation.Jacquet.OppositeCanonicalLiftProof
Langlands.Representation.Jacquet.OppositeCanonicalLiftStatement
Langlands.Representation.Jacquet.Parabolic
Langlands.Representation.Jacquet.PositiveCharacter
Langlands.Representation.Jacquet.ReciprocityProof
Langlands.Representation.Jacquet.ReciprocityStatement
Langlands.Representation.Jacquet.RefinedOppositeCanonicalLiftProof
Langlands.Representation.Jacquet.RefinedOppositeCanonicalLiftStatement
Langlands.Representation.Jacquet.RefinedOppositeCompressionProof
Langlands.Representation.Jacquet.RefinedOppositeCompressionStatement
Langlands.Representation.Jacquet.RefinedOppositePowerKernelProof
Langlands.Representation.Jacquet.RefinedOppositeStableImageProof
Langlands.Representation.Jacquet.RefinedUpperCanonicalLiftProof
Langlands.Representation.Jacquet.SmoothTwist
Langlands.Representation.Jacquet.StablePairingProof
Langlands.Representation.MatrixCoefficient.Definitions
Langlands.Representation.MatrixCoefficient.LawsProof
Langlands.Representation.MatrixCoefficient.LawsStatement
Langlands.Representation.MatrixCoefficient.ModuloCenter
Langlands.Representation.Mirabolic.MixedProducts
Langlands.Representation.OrbitSpan
Langlands.Representation.Parabolic.AdmissibilityStatement
Langlands.Representation.Parabolic.ComposedFunctors
Langlands.Representation.Parabolic.FlattenedRefinementModulusCalculation
Langlands.Representation.Parabolic.GeometricPrerequisitesStatement
Langlands.Representation.Parabolic.HeadTailProductInduction
Langlands.Representation.Parabolic.InducedMapSurjectivity
Langlands.Representation.Parabolic.InductionFactorMatchingProof
Langlands.Representation.Parabolic.InductionFactorMatchingStatement
Langlands.Representation.Parabolic.InductionSubrepresentation
Langlands.Representation.Parabolic.LeviBridges
Langlands.Representation.Parabolic.LeviInflationAdmissibilityProof
Langlands.Representation.Parabolic.NaturalFirstAdjointness
Langlands.Representation.Parabolic.NaturalInductionDualityFromScalar
Langlands.Representation.Parabolic.NaturalInductionDualityProof
Langlands.Representation.Parabolic.NaturalInductionDualityStatement
Langlands.Representation.Parabolic.NaturalJacquetDualityProof
Langlands.Representation.Parabolic.NaturalJacquetDualityStatement
Langlands.Representation.Parabolic.NormalizedAdmissibilityProof
Langlands.Representation.Parabolic.NormalizedInductionStatement
Langlands.Representation.Parabolic.NormalizedJacquetAdmissibilityProof
Langlands.Representation.Parabolic.NormalizedJacquetExactnessProof
Langlands.Representation.Parabolic.NormalizedJacquetStatement
Langlands.Representation.Parabolic.OppositeJacquetAdmissibilityProof
Langlands.Representation.Parabolic.OppositeJacquetAdmissibilityStatement
Langlands.Representation.Parabolic.OppositeRefinementDefinitions
Langlands.Representation.Parabolic.OppositeRefinementFunctors
Langlands.Representation.Parabolic.OppositeRefinementTransitivityProof
Langlands.Representation.Parabolic.OppositeRefinementTransitivityStatement
Langlands.Representation.Parabolic.OrderedProductRegroupingEquivalence
Langlands.Representation.Parabolic.OrderedProductRegroupingProof
Langlands.Representation.Parabolic.OrderedProductRegroupingStatement
Langlands.Representation.Parabolic.ProductInductionSubrepresentation
Langlands.Representation.Parabolic.QuotientCompactProof
Langlands.Representation.Parabolic.RefinedInductionAdmissibility
Langlands.Representation.Parabolic.RefinedInductionTensorMap
Langlands.Representation.Parabolic.RefinedInductionTensorNormalization
Langlands.Representation.Parabolic.RefinedInductionTensorProof
Langlands.Representation.Parabolic.RefinedInductionTensorStatement
Langlands.Representation.Parabolic.RefinementCharacter
Langlands.Representation.Parabolic.RefinementComposition
Langlands.Representation.Parabolic.RefinementCoordinatesNormalizationProof
Langlands.Representation.Parabolic.RefinementCoordinatesNormalizationStatement
Langlands.Representation.Parabolic.RefinementInductionTransitivityProof
Langlands.Representation.Parabolic.RefinementPreimage
Langlands.Representation.Parabolic.RefinementTransitivityStatement
Langlands.Representation.Parabolic.RegroupingFactorEquivalences
Langlands.Representation.Parabolic.SecondAdjointnessAssembly
Langlands.Representation.Parabolic.SecondAdjointnessProof
Langlands.Representation.Parabolic.SecondAdjointnessStatement
Langlands.Representation.Parabolic.StandardOppositeJacquetAdmissibilityProof
Langlands.Representation.Parabolic.ThreeBlockCarrierComparison
Langlands.Representation.Parabolic.ThreeBlockInductionAssociativityStatement
Langlands.Representation.Parabolic.ThreeBlockRefinementGeometry
Langlands.Representation.Parabolic.ThreeBlockRegroupingAssembly
Langlands.Representation.Parabolic.ThreeBlockUniverseReduction
Langlands.Representation.Parabolic.UnipotentFiniteContainment
Langlands.Representation.RankinSelberg.GeneralLinearUnimodularity
Langlands.Representation.RankinSelberg.Measures
Langlands.Representation.RankinSelberg.UnimodularityStatement
Langlands.Representation.RankinSelberg.UnipotentUnimodularity
Langlands.Representation.Schur.CountableDimensionProof
Langlands.Representation.Schur.CountableDimensionStatement
Langlands.Representation.Shahidi.Geometry
Langlands.Representation.Shahidi.Induction
Langlands.Representation.Shahidi.TwoBlocks
Langlands.Representation.Smooth.Admissibility.CofinalProof
Langlands.Representation.Smooth.Admissibility.CofinalStatement
Langlands.Representation.Smooth.Admissibility.EmbeddingProof
Langlands.Representation.Smooth.Admissibility.EmbeddingStatement
Langlands.Representation.Smooth.Admissibility.EquivalenceProof
Langlands.Representation.Smooth.Admissibility.EquivalenceStatement
Langlands.Representation.Smooth.Admissibility.Extension
Langlands.Representation.Smooth.Contragredient.AdmissibleDualityProof
Langlands.Representation.Smooth.Contragredient.AdmissibleDualityStatement
Langlands.Representation.Smooth.Contragredient.CompactDualityProof
Langlands.Representation.Smooth.Contragredient.CompactDualityStatement
Langlands.Representation.Smooth.Contragredient.Definitions
Langlands.Representation.Smooth.Contragredient.ExactProof
Langlands.Representation.Smooth.Contragredient.ExactStatement
Langlands.Representation.Smooth.Contragredient.FixedVectorsDefinitions
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
Langlands.Representation.Smooth.FixedVectors.Definitions
Langlands.Representation.Smooth.FixedVectors.Detection
Langlands.Representation.Smooth.FixedVectors.FiniteTypes
Langlands.Representation.Smooth.FixedVectors.FiniteTypesStatement
Langlands.Representation.Smooth.FixedVectors.GenerationInheritance
Langlands.Representation.Smooth.FixedVectors.GenerationInheritanceStatement
Langlands.Representation.Smooth.FixedVectors.LawsProof
Langlands.Representation.Smooth.FixedVectors.LawsStatement
Langlands.Representation.Smooth.FixedVectors.OrderProof
Langlands.Representation.Smooth.FixedVectors.OrderStatement
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
Langlands.Representation.Tensor.ExternalMapSurjectivityProof
Langlands.Representation.Tensor.ExternalMapSurjectivityStatement
Langlands.Representation.Tensor.ExternalSubquotient
Langlands.Representation.Tensor.ExternalSubrepresentation
Langlands.Representation.Tensor.Filtration
Langlands.Representation.Tensor.Finite
Langlands.Representation.Tensor.FiniteEquivalences
Langlands.Representation.Tensor.FiniteFiltration
Langlands.Representation.Tensor.FiniteProperties
Langlands.Representation.Tensor.FiniteRegrouping
Langlands.Representation.Tensor.GLRefinement
Langlands.Representation.Tensor.OneFactor
Langlands.Representation.Tensor.ProductFiltration
Langlands.Representation.Tensor.SmoothSubquotients
Langlands.Representation.Twist.AdmissibilityProof
Langlands.Representation.Twist.AdmissibilityStatement
Langlands.Representation.Twist.AlgebraProof
Langlands.Representation.Twist.AlgebraStatement
Langlands.Representation.Twist.ContinuousCharacterProof
Langlands.Representation.Twist.ContinuousCharacterStatement
Langlands.Representation.Twist.Definitions
Langlands.Representation.Twist.DualProof
Langlands.Representation.Twist.DualStatement
Langlands.Representation.Twist.LeviComplexPower
Langlands.Representation.Twist.LeviRealPower
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
Langlands.Representation.Whittaker.Algebraic
Langlands.Representation.Whittaker.GeneralLinear
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

## External import frontier

```text
Lean.Elab.Tactic.Omega
Mathlib.Algebra.Algebra.NonUnitalHom
Mathlib.Algebra.Algebra.NonUnitalSubalgebra
Mathlib.Algebra.Algebra.Subalgebra.Lattice
Mathlib.Algebra.BigOperators.Fin
Mathlib.Algebra.BigOperators.Finprod
Mathlib.Algebra.BigOperators.Group.Finset.Basic
Mathlib.Algebra.BigOperators.GroupWithZero.Action
Mathlib.Algebra.BigOperators.Pi
Mathlib.Algebra.Category.ModuleCat.Basic
Mathlib.Algebra.CharP.Basic
Mathlib.Algebra.DirectSum.Module
Mathlib.Algebra.Exact.Basic
Mathlib.Algebra.Field.Subfield.Basic
Mathlib.Algebra.Group.Equiv.TypeTags
Mathlib.Algebra.Group.Hom.Instances
Mathlib.Algebra.Group.Pi.Lemmas
Mathlib.Algebra.Group.Subgroup.Ker
Mathlib.Algebra.Group.Subgroup.Pointwise
Mathlib.Algebra.Group.Submonoid.Basic
Mathlib.Algebra.Group.TypeTags.Finite
Mathlib.Algebra.Group.TypeTags.Hom
Mathlib.Algebra.Module.Projective
Mathlib.Algebra.Module.Submodule.Map
Mathlib.Algebra.Module.ULift
Mathlib.Algebra.Order.Archimedean.Basic
Mathlib.Algebra.Order.BigOperators.Group.Finset
Mathlib.Algebra.Polynomial.Lifts
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
Mathlib.Analysis.SpecialFunctions.Pow.Complex
Mathlib.Analysis.SpecialFunctions.Pow.NNReal
Mathlib.Analysis.SpecialFunctions.Pow.Real
Mathlib.Analysis.SpecialFunctions.Sqrt
Mathlib.Analysis.SpecificLimits.Basic
Mathlib.Basic.Complex.Basic
Mathlib.CategoryTheory.Abelian.Subcategory
Mathlib.CategoryTheory.Discrete.Basic
Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
Mathlib.CategoryTheory.Pi.Basic
Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
Mathlib.CategoryTheory.Products.Basic
Mathlib.CategoryTheory.Skeletal
Mathlib.CategoryTheory.Whiskering
Mathlib.Combinatorics.Enumerative.Composition
Mathlib.Data.ENat.Basic
Mathlib.Data.ENat.BigOperators
Mathlib.Data.Fin.Rev
Mathlib.Data.Fin.Tuple.Sort
Mathlib.Data.Fintype.EquivFin
Mathlib.Data.Fintype.Quotient
Mathlib.Data.Fintype.Sort
Mathlib.Data.Int.Cast.Lemmas
Mathlib.Data.Int.Interval
Mathlib.Data.Int.LeastGreatest
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
Mathlib.FieldTheory.RatFunc.AsPolynomial
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
Mathlib.GroupTheory.Subgroup.Center
Mathlib.GroupTheory.Subgroup.Centralizer
Mathlib.GroupTheory.Transfer
Mathlib.LinearAlgebra.AffineSpace.AffineMap
Mathlib.LinearAlgebra.Basis.VectorSpace
Mathlib.LinearAlgebra.Charpoly.Basic
Mathlib.LinearAlgebra.Charpoly.ToMatrix
Mathlib.LinearAlgebra.Determinant
Mathlib.LinearAlgebra.Dimension.Basic
Mathlib.LinearAlgebra.Dimension.Constructions
Mathlib.LinearAlgebra.DirectSum.Finite
Mathlib.LinearAlgebra.Dual.Lemmas
Mathlib.LinearAlgebra.Eigenspace.Basic
Mathlib.LinearAlgebra.Eigenspace.Pi
Mathlib.LinearAlgebra.Eigenspace.Triangularizable
Mathlib.LinearAlgebra.FiniteDimensional.Basic
Mathlib.LinearAlgebra.FiniteDimensional.Defs
Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
Mathlib.LinearAlgebra.Finsupp.LinearCombination
Mathlib.LinearAlgebra.Finsupp.VectorSpace
Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
Mathlib.LinearAlgebra.Isomorphisms
Mathlib.LinearAlgebra.Matrix.Block
Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
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
Mathlib.LinearAlgebra.PiTensorProduct.Finite
Mathlib.LinearAlgebra.PiTensorProduct.Generators
Mathlib.LinearAlgebra.Projection
Mathlib.LinearAlgebra.Quotient.Basic
Mathlib.LinearAlgebra.Semisimple
Mathlib.LinearAlgebra.TensorProduct.Basis
Mathlib.LinearAlgebra.TensorProduct.Finiteness
Mathlib.LinearAlgebra.TensorProduct.RightExactness
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
Mathlib.MeasureTheory.Measure.Lebesgue.Basic
Mathlib.MeasureTheory.Measure.OpenPos
Mathlib.MeasureTheory.Measure.Regular
Mathlib.MeasureTheory.Measure.Typeclasses.Finite
Mathlib.NumberTheory.LocalField.Basic
Mathlib.NumberTheory.Padics.LocalField
Mathlib.NumberTheory.Padics.RingHoms
Mathlib.Order.Atoms
Mathlib.Order.CompactlyGenerated.Basic
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
Mathlib.RingTheory.Algebraic.LinearIndependent
Mathlib.RingTheory.Artinian.Module
Mathlib.RingTheory.DedekindDomain.IntegralClosure
Mathlib.RingTheory.FiniteLength
Mathlib.RingTheory.Finiteness.Basic
Mathlib.RingTheory.Flat.Basic
Mathlib.RingTheory.Ideal.Quotient.Operations
Mathlib.RingTheory.Jacobson.Semiprimary
Mathlib.RingTheory.Length
Mathlib.RingTheory.Nakayama
Mathlib.RingTheory.Nilpotent.Basic
Mathlib.RingTheory.Noetherian.Basic
Mathlib.RingTheory.Noetherian.Defs
Mathlib.RingTheory.Norm.Transitivity
Mathlib.RingTheory.Polynomial.Basic
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
Mathlib.Topology.Instances.Real.Lemmas
Mathlib.Topology.LocallyClosed
Mathlib.Topology.LocallyConstant.Algebra
Mathlib.Topology.LocallyConstant.Basic
Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
Mathlib.Topology.Order.Compact
Mathlib.Topology.Separation.Profinite
Mathlib.Topology.UrysohnsLemma
```
