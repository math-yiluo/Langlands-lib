# Actual comparisons of head products with equal cuspidal content

Author: Worker 357.

For two supplied positive-rank products of special heads with equal exact
cuspidal contents, irreducibility of the first gives an actual equivalence
from that whole product to a detected irreducible constituent of the second.
The whole first product is consequently an actual smooth subquotient of the
second, and this occurrence passes through every actual derivative.
The construction composes published actual cuspidal quotients, top-derivative
nontriviality and fixed-support equivalences. It does not prove either
direction of the full special-head product irreducibility criterion.

## Exact interface and conventions

The parameters are every `{p : ℕ} [Fact p.Prime]`, an actual
`F : PadicField.{uF} p`, its supplied `T : F.TopologicalData`, and a bundled
continuous nontrivial unitary additive character `ψ` for `T.topology`.
The field universe `uF` and the original cuspidal carrier universe `uV`
are independent.

Let `d e : T.SegmentProductDatum.{uV,uF} n`. Their segment bases remain in
`CuspidalDatum.{uV,uF} T`, and their blocks and induced products have carrier
universe `max uF uV`. The existing `HasSegmentHeads` relation specifies the
strong head of each increasing segment induction. It is the special-head
convention, distinct from the increasing induction's segment socle.
All lists and multisets retain repeated occurrences.

`segmentHeadProductSubquotientCuspidalSupportIndependent T d hd E hE hEd`
proves

```text
T.IsSupercuspidalSupport E d.multisegment.cuspidalContent.
```

Here `hd : d.HasSegmentHeads`, `E` is an actual smooth object on `GL_n(F)`
in carrier universe `max uF uV`, `hE` is its irreducibility, and
`hEd : SmoothRep.IsSubquotient E d.induced`. This helper permits rank zero
and requires no additive character. It supplies one support witness and
does not invoke uniqueness of supercuspidal support.

`SegmentHeadProductComparisonData T ψ d e` retains two fields:

- `detected : ExactFunctorDetectedConstituent.Data J e.induced`, where
  `J = generalLinearDerivative T ψ n n le_rfl`. This includes an actual
  constituent, its irreducibility, its actual occurrence in `e.induced`,
  nontriviality of its top derivative, and the existing equivalences to all
  detected irreducible subquotients of this same second product.
- `equivalence`, an actual equivariant complex-linear equivalence from
  `d.induced.representation` to `detected.constituent.representation`.

`segmentHeadProductComparison T ψ hn d e hd he hirr hcontent` constructs
these data assuming exactly

```text
hn       : 0 < n
hd       : d.HasSegmentHeads
he       : e.HasSegmentHeads
hirr     : d.induced.IsIrreducible
hcontent : d.multisegment.cuspidalContent = e.multisegment.cuspidalContent.
```

The second product need not be irreducible. There is no ordering,
nonlinkage, distinctness or equality-of-multisegments premise. The equality
is of the full cuspidal multisets, including multiplicities, rather than
their underlying sets. No representative, support-realization, finite-length
or top-nonvanishing premise is added to this public constructor.

For any supplied `c : SegmentHeadProductComparisonData T ψ d e`,
`c.isSubquotient T` proves
`SmoothRep.IsSubquotient d.induced e.induced`.
For every `k : ℕ` and `hk : k ≤ n`, `c.derivative_isSubquotient T k hk`
proves

```text
SmoothRep.IsSubquotient
  ((generalLinearDerivative T ψ n k hk).obj d.induced)
  ((generalLinearDerivative T ψ n k hk).obj e.induced).
```

This includes order zero and the full top order. It requires no
nontriviality or irreducibility of either derivative. All source and
derivative objects use the same carrier universe `max uF uV`; there is no
comparison between derivative functors in different universes.

## Implemented construction

For the support helper, set
`C := segmentHeadProductCuspidalQuotient T d hd`. Its actual member family,
content equality, rank sum and represented supercuspidal factors supply
all the nonoccurrence fields of the support witness. Its surjective
`quotientMap` exhibits `d.induced` as a quotient, hence a subquotient, of
the actual cuspidal product on those factors.
The general `smoothSubquotientTransitivity` composes this occurrence with
the supplied occurrence of `E` in `d.induced`. The irreducibility field is
exactly `hE`. No choice of a different support is made.

For the constructor, choose
`c := chooseSegmentHeadProductDetectedConstituent T ψ hn e he`.
This published constructor applies exact-functor constituent extraction
to the supplied second product, using its proved finite length and scalar
top derivative. Its fields supply `c.irreducible`, `c.occurs` and
`c.image_nontrivial`.

The first product has support `d.multisegment.cuspidalContent` by the
published `segmentHeadProductCuspidalSupportIndependent`, using exactly
`hirr`. Apply the new support helper to `c.constituent` with
`c.irreducible` and `c.occurs`; rewrite its support using `hcontent` to
the same multiset as the first. The published
`segmentHeadProductTopDerivativeNontrivial T ψ hn d hd` gives top
nontriviality for the first product.
Now `CuspidalSupport.fixedSupportDetectedEquiv` gives the actual
equivalence from the first product to `c.constituent`. Pair it with `c`.
All representation choices occur in these published noncomputable
constructions; the new constructor does not assume their existence as
extra inputs.

The fixed-support comparison uses a finite-index matching of occurrences,
actual representative transport, the general cuspidal-association theorem
for matching Jordan–Hölder factors of permuted cuspidal products, and the
published exact-functor equivalences within one fixed cuspidal product.
It does not assume an actual commutation isomorphism for arbitrary induced
products, or any segment-product uniqueness conclusion.

For `isSubquotient`, `SmoothRep.mkIso c.equivalence.symm` is an isomorphism
from the stored constituent to the whole first product.
`SmoothRep.IsSubquotient.of_iso_left` transports the stored occurrence in
that direction. In this API an isomorphism `B ≅ B'` transports an
occurrence of `B` to an occurrence of `B'`; the inverse equivalence is
therefore essential.

For `derivative_isSubquotient`, apply the published
`ExactSmoothTransport.map_isSubquotient` to that occurrence and the
published `generalLinearDerivativeExactness F T ψ n k hk`. The generic
transport proof represents a subquotient by an actual intermediate object,
an injective inclusion and a surjective quotient map. Exactness preserves
the injectivity and surjectivity of their images. The same presentation
therefore gives an actual smooth subquotient after applying the derivative.
This step uses no formula for an individual segment derivative.

## Derived provenance and scope

This pair assembles existing actual constructions and generic subquotient
transport. It introduces no new literature assertion and has derived
provenance with no source tuples. Its mathematical inputs and conventions
are documented in the published
[fixed-support comparison](../CuspidalSupport/FixedSupportDetectedEquiv.md),
[cuspidal quotient](SegmentHeadProductCuspidalQuotient.md), and
[top derivative](SegmentHeadProductTopDerivative.md) pairs.
Only published results are reused; no unreviewed draft is adapted.

The constructor needs the displayed irreducibility of the first product.
It does not establish that premise, prove irreducibility of the second,
identify either whole product with the other, prove survival of every
simple subquotient under the top derivative, or identify any intermediate
segment derivative with a head. It does not construct linked replacement
data or an occurrence obstruction. The arbitrary-family reduction and
both directions of `SegmentHeadProductIrreducibility` remain obligations
of the host.

## Complete dependency and independence audit

The entry imports precisely these three published project modules, with
the common prefix `Langlands.Representation.`:

| Import | Used interface and mathematical route |
| --- | --- |
| `CuspidalSupport.FixedSupportDetectedEquiv` | Actual equivalence for irreducible objects with the same multiset support and nonzero top derivatives; finite fiber matching, actual tensor permutation, general cuspidal association and generic detected-constituent equivalences |
| `Classification.SegmentHeadProductCuspidalQuotient` | Actual cuspidal member representatives and surjective map to the supplied head product, and its support corollary; primitive strong-head quotients, tensor and induction surjectivity, ordered regrouping and finite member flattening |
| `Classification.SegmentHeadProductTopDerivative` | Nontrivial full top derivative of the first product and actual detected constituent of the second; permitted individual-head top derivative, general finite-product top line, exactness, finite length and composition-series extraction |

The author read these three Lean bodies, their exact-interface,
implemented-proof and independence explanations, and the actual
`ExactFunctorDetectedConstituent.Data`, subquotient-transitivity and
exact-subquotient-transport bodies. The recursive inventory below records
all project imports and the external import frontier. It was generated
after stripping nested comments and string literals from Lean. Every
inherited Lean/Markdown pair equals the current published Library
`b01e426d540ff0d2edcc0480f6f0d03dd2f71e78` byte for byte. The refresh has no
conflicts. All project modules have nonempty Markdown pairs, and the scan
finds no proof hole, new axiom, prohibited execution syntax, or scanned
excluded declaration/task name.

This combines a used-interface and proof-route audit with complete
recursive import and byte-equality checks. It does not claim that every
inherited proof body was newly read line by line.
The private reproducibility inventory is
`.private/notes/worker357-head-product-comparison-import-audit-2026-11-04.json`;
the complete public lists below reconstruct its module sets.

The lower mathematical routes remain those of the three published inputs.
The individual-head top proof embeds the supplied strong head into
decreasing cuspidal induction, applies the independently proved general
BZ77 4.11 theorem to its nonzero mirabolic range, and uses general
Gelfand–Kazhdan multiplicity one and admissibility for the scalar line.
Its actual head embedding uses permitted individual-head existence and
cuspidal-induction Jacquet multiplicities. These are different from full
head/socle segment Jacquet formulas.
The finite-product top line follows from general induction regrouping,
the proved Leibniz filtration and its sole feasible top grade, together
with rank-zero tensor comparison. General exactness and finite length,
followed by generic composition-series image extraction, supply the actual
detected constituent. The exact-functor conditional irreducibility
criterion imported in that branch is not applied in this module.

All six trusted operator files were read in full:

- [bd71b9185aab5d6eafffb7891bd3a3ca](/home/taskhub/pilot/correspondence/bd71b9185aab5d6eafffb7891bd3a3ca.md)
  permits the fully proved general derivative route and preserves the
  segment-formula and classification exclusions.
- [0edda6122ce65ed7ac51603c37473920](/home/taskhub/pilot/correspondence/0edda6122ce65ed7ac51603c37473920.md)
  permits independently accepted and published BZ77 4.11, general Ze80
  3.7(b) through Lemma 4.7(b), Ze80 5.3 and nine generic modules.
- [30144f6f9b59540b88b6d4c1517892d9](/home/taskhub/pilot/correspondence/30144f6f9b59540b88b6d4c1517892d9.md)
  permits a separately proved support-only derivative bound.
- [ed80148e21e7523abfc048f455e98eb0](/home/taskhub/pilot/correspondence/ed80148e21e7523abfc048f455e98eb0.md)
  restricts `core_mid` and its consequence to that bound's length-two base.
- [2b33898bdd0a5ff1b9031be5155a06f0](/home/taskhub/pilot/correspondence/2b33898bdd0a5ff1b9031be5155a06f0.md)
  and [ca18fd5005bf5e12a3f7cade18dca865](/home/taskhub/pilot/correspondence/ca18fd5005bf5e12a3f7cade18dca865.md)
  restrict the adjacent-supercuspidal reducibility exception.

Only the general foundations and individual-head constructions authorized
by the first two rulings enter here. This closure needs no support-only
bound, `core_mid`, its at-most-one-factor consequence or the restricted
reducibility exception.

The nine authorized generic modules occur with unchanged published bytes.
With prefix `Langlands.Representation.` except where stated, these are
`Filtration.ObjectTransport`, `Tensor.FiniteFiltration`,
`Tensor.ExternalFiltration`, `Tensor.ExternalSubrepresentation`,
`Parabolic.InductionSubrepresentation`,
`Parabolic.ProductInductionSubrepresentation`,
`Langlands.Combinatorics.RelationInversions`,
`Derivative.MirabolicMinusNormalization` and
`Classification.SupercuspidalDerivativesStatement`.
Their uses are actual filtration/tensor transport, induction of actual
subrepresentations, finite inversion bookkeeping, general minus-functor
normalization and the isolated cuspidal derivative predicate with its
independently proved theorem. Their introducing tasks' excluded
conclusions are not used.

The following exclusions are retained directly and transitively, including
renamed conclusions and proof successors:

- Parent `GenericSegmentProductUniqueness`,
  `30341ae4-65f2-4a0e-9283-763db01a409e`; multisegment exhaustion,
  `3bfb61fa-1129-4fc9-83fd-7fcfec22106e`; ordered strong-head existence,
  `ebea9a8a-9b21-4208-aa31-98c2dea1f8a3`; quotient coverage,
  `20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584`; and ordered conversion,
  `8252833d-c269-41a9-824c-5879e531b23b`.
- Tempered uniqueness, `52e97845-36bb-457d-b76f-70753334b88c`;
  `SquareIntegrableLanglandsClassification`,
  `1cb45da2-7007-4351-a694-594fb148b8d1`; square-integrable exhaustion,
  `cd8ab97c-0b78-4bce-97c4-d307a28159a4`; and regular exhaustion,
  `bf433f0a-921a-428c-b0c0-6475438125ac`.
- Ze80 3.5/9.6 segment derivative formulas, the segment-socle derivative
  part of `8e5b4563-0365-41c7-b134-70f2a0b36292`, full/head/socle
  segment Jacquet formulas and exponent-norm formula, including
  `ed48ae06-964c-4c84-9e62-978f5a953ca7`,
  `55ad1e10-62d8-46b7-a081-909ef0056426`,
  `b95105c6-f8bb-4641-ae53-2f49d1e7f034` and
  `92aea10f-62ac-4e0b-bd4a-9a80909797c5`.
- Segment-socle product irreducibility, linked structure, gluing,
  commutation, swaps and socle exhaustion, including
  `2ae5cbe5-0701-4509-88a0-db8cbeb35be4`; analytic segment
  classification, special square-integrability, two-supercuspidal
  product structure/irreducibility and Whittaker coinvariant finiteness.
- The host `SegmentHeadProductIrreducibility` conclusion in either
  direction, task `8364e73f-14ec-4d14-8f2b-1555a7c1ce95`. Already
  published supporting constructions from this host do not assume it.

In particular, the closure contains no `SegmentHeadSupportStep`,
`SegmentHeadJacquetReduction`, `TwoSupercuspidalProductStructureProof`,
`UniverseLiftPadic` or restricted support-proof intermediate.
Essential/tempered and analytic segment statement modules inherited
through individual-head infrastructure supply definitions or Prop targets;
no unproved statement is used as a theorem. Reuse is by current published
Lean names, with no pending input or conditional classification assembly.

## Development verification

Recovery check `b20d42e1-ed59-4b87-acf3-06d11bbe887f` compiled the published
original-occurrence module and this comparison with zero errors or
warnings. Exact inspection `e27f15a1-4e02-409e-8215-1a70ebd9901b` of
`segmentHeadProductComparison` again compiled without errors or warnings
and reports a definition with independent universe parameters `uF`, `uV`
and only `propext`, `Classical.choice` and `Quot.sound`. These are
development checks; independent semantic acceptance and integration are
separate requirements for the new pair.

## Complete recursive project import inventory

The closure has 1,149 project modules, including this entry; all 1,148 inherited pairs were checked against the Library named above.

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
- `Langlands.HarmonicAnalysis.RowFourier`
- `Langlands.HarmonicAnalysis.RowSchwartzAction`
- `Langlands.HarmonicAnalysis.RowTensorDecompositionProof`
- `Langlands.HarmonicAnalysis.RowTensorDecompositionStatement`
- `Langlands.HarmonicAnalysis.RowTestSmoothProof`
- `Langlands.HarmonicAnalysis.RowTestSmoothStatement`
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
- `Langlands.Representation.Classification.FiniteLengthProof`
- `Langlands.Representation.Classification.FiniteLengthStatement`
- `Langlands.Representation.Classification.HeadQuotientCriterionProof`
- `Langlands.Representation.Classification.HeadQuotientCriterionStatement`
- `Langlands.Representation.Classification.IrreducibleProductEmbedding`
- `Langlands.Representation.Classification.IrreducibleProductEmbeddingStatement`
- `Langlands.Representation.Classification.IrreducibleProductFiniteLengthProof`
- `Langlands.Representation.Classification.LanglandsData`
- `Langlands.Representation.Classification.MirabolicDerivativeContragredient`
- `Langlands.Representation.Classification.MultiplicityOneConstituentProof`
- `Langlands.Representation.Classification.MultiplicityOneConstituentStatement`
- `Langlands.Representation.Classification.NormalizedProductFiniteLengthStatement`
- `Langlands.Representation.Classification.OppositeCuspidalJacquetFiltrationProof`
- `Langlands.Representation.Classification.OppositeCuspidalJacquetFiltrationStatement`
- `Langlands.Representation.Classification.OppositeJacquetQuotientDetectionProof`
- `Langlands.Representation.Classification.OppositeJacquetQuotientDetectionStatement`
- `Langlands.Representation.Classification.OppositeJacquetReciprocity`
- `Langlands.Representation.Classification.OppositeSupportJacquetAdapter`
- `Langlands.Representation.Classification.SegmentConstituentStatement`
- `Langlands.Representation.Classification.SegmentCuspidalContent`
- `Langlands.Representation.Classification.SegmentDecreasingCuspidalProduct`
- `Langlands.Representation.Classification.SegmentHeadDecreasingSocle`
- `Langlands.Representation.Classification.SegmentHeadProductComparison`
- `Langlands.Representation.Classification.SegmentHeadProductCuspidalQuotient`
- `Langlands.Representation.Classification.SegmentHeadProductFiniteness`
- `Langlands.Representation.Classification.SegmentHeadProductTopDerivative`
- `Langlands.Representation.Classification.SegmentHeadTopDerivative`
- `Langlands.Representation.Classification.SegmentInductionAdmissibilityProof`
- `Langlands.Representation.Classification.SegmentInductionAdmissibilityStatement`
- `Langlands.Representation.Classification.SegmentJacquetMultiplicityProof`
- `Langlands.Representation.Classification.SegmentJacquetMultiplicityStatement`
- `Langlands.Representation.Classification.SegmentJacquetReversal`
- `Langlands.Representation.Classification.SegmentProductCuspidalMembers`
- `Langlands.Representation.Classification.SegmentSpecialConstituentExistenceProof`
- `Langlands.Representation.Classification.SegmentTensorReversalProof`
- `Langlands.Representation.Classification.SegmentTensorReversalStatement`
- `Langlands.Representation.Classification.SegmentTensorStabilizerProof`
- `Langlands.Representation.Classification.SegmentTensorStabilizerStatement`
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
- `Langlands.Representation.CuspidalSupport.AssociationReverseProof`
- `Langlands.Representation.CuspidalSupport.AssociationReverseStatement`
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
- `Langlands.Representation.CuspidalSupport.DistinctTensorStabilizerProof`
- `Langlands.Representation.CuspidalSupport.DistinctTensorStabilizerStatement`
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
- `Langlands.Representation.CuspidalSupport.WholeLeviTransport`
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
- `Langlands.Representation.Derivative.LeftMixedProductHomogeneityProof`
- `Langlands.Representation.Derivative.LeftMixedProductHomogeneityStatement`
- `Langlands.Representation.Derivative.LeftMixedProductPhiHatIterate`
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
- `Langlands.Representation.Derivative.TopProduct`
- `Langlands.Representation.Derivative.ZeroRankTensor`
- `Langlands.Representation.Dual.Definitions`
- `Langlands.Representation.Exponents.Central`
- `Langlands.Representation.Exponents.DualJacquet`
- `Langlands.Representation.Exponents.DualJacquetStatement`
- `Langlands.Representation.Exponents.Jacquet`
- `Langlands.Representation.Exponents.NilpotenceIndex`
- `Langlands.Representation.Exponents.ParabolicPair`
- `Langlands.Representation.Exponents.UnitaryDualJacquetSupportAdapters`
- `Langlands.Representation.Filtration.ActualGradedExtraction`
- `Langlands.Representation.Filtration.CoinvariantVanishingStatement`
- `Langlands.Representation.Filtration.CommonSubquotientStatement`
- `Langlands.Representation.Filtration.Definitions`
- `Langlands.Representation.Filtration.ExactConstituentExtraction`
- `Langlands.Representation.Filtration.ExactFunctorDetectedConstituent`
- `Langlands.Representation.Filtration.ExactFunctorIrreducibility`
- `Langlands.Representation.Filtration.ExactSmoothSubquotients`
- `Langlands.Representation.Filtration.ExactSmoothTransport`
- `Langlands.Representation.Filtration.FactorMatchingPullback`
- `Langlands.Representation.Filtration.FiniteFamilyMultiplicityProof`
- `Langlands.Representation.Filtration.FiniteFamilyMultiplicityStatement`
- `Langlands.Representation.Filtration.GluedFamily`
- `Langlands.Representation.Filtration.GradedRefinementProof`
- `Langlands.Representation.Filtration.GradedRefinementStatement`
- `Langlands.Representation.Filtration.IntervalLiftProof`
- `Langlands.Representation.Filtration.IntervalLiftStatement`
- `Langlands.Representation.Filtration.InvariantBilinear`
- `Langlands.Representation.Filtration.InvariantBilinearBounds`
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
- `Langlands.Representation.MatrixCoefficient.LawsProof`
- `Langlands.Representation.MatrixCoefficient.LawsStatement`
- `Langlands.Representation.MatrixCoefficient.ModuloCenter`
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
- `Langlands.Representation.Parabolic.InducedMapSurjectivity`
- `Langlands.Representation.Parabolic.InductionFactorMatchingProof`
- `Langlands.Representation.Parabolic.InductionFactorMatchingStatement`
- `Langlands.Representation.Parabolic.InductionSubrepresentation`
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
- `Langlands.Representation.Parabolic.NormalizedInductionStatement`
- `Langlands.Representation.Parabolic.NormalizedJacquetAdmissibilityProof`
- `Langlands.Representation.Parabolic.NormalizedJacquetExactnessProof`
- `Langlands.Representation.Parabolic.NormalizedJacquetStatement`
- `Langlands.Representation.Parabolic.OppositeJacquetAdmissibilityProof`
- `Langlands.Representation.Parabolic.OppositeJacquetAdmissibilityStatement`
- `Langlands.Representation.Parabolic.OppositeRefinementDefinitions`
- `Langlands.Representation.Parabolic.OppositeRefinementFunctors`
- `Langlands.Representation.Parabolic.OppositeRefinementTransitivityProof`
- `Langlands.Representation.Parabolic.OppositeRefinementTransitivityStatement`
- `Langlands.Representation.Parabolic.OrderedProductRegroupingEquivalence`
- `Langlands.Representation.Parabolic.OrderedProductRegroupingProof`
- `Langlands.Representation.Parabolic.OrderedProductRegroupingStatement`
- `Langlands.Representation.Parabolic.OrderedRefinementInduction`
- `Langlands.Representation.Parabolic.OrderedRefinementTensorInduction`
- `Langlands.Representation.Parabolic.ProductInductionSubrepresentation`
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
- `Langlands.Representation.Tensor.ExternalFiltration`
- `Langlands.Representation.Tensor.ExternalMapSurjectivityProof`
- `Langlands.Representation.Tensor.ExternalMapSurjectivityStatement`
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
- `Langlands.Representation.Twist.AdmissibilityProof`
- `Langlands.Representation.Twist.AdmissibilityStatement`
- `Langlands.Representation.Twist.AlgebraProof`
- `Langlands.Representation.Twist.AlgebraStatement`
- `Langlands.Representation.Twist.ContinuousCharacterProof`
- `Langlands.Representation.Twist.ContinuousCharacterStatement`
- `Langlands.Representation.Twist.Definitions`
- `Langlands.Representation.Twist.DualProof`
- `Langlands.Representation.Twist.DualStatement`
- `Langlands.Representation.Twist.RealPower`
- `Langlands.Representation.Twist.SmoothPartDefinitions`
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

## Complete external import frontier

These 300 names are the external imports occurring directly in the project closure; they are not a traversal of Mathlib internals.

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
- `Mathlib.Algebra.BigOperators.Ring.Finset`
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
- `Mathlib.LinearAlgebra.Matrix.Rank`
- `Mathlib.LinearAlgebra.Matrix.Reindex`
- `Mathlib.LinearAlgebra.Matrix.SchurComplement`
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
- `Mathlib.LinearAlgebra.TensorProduct.RightExactness`
- `Mathlib.LinearAlgebra.Trace`
- `Mathlib.Logic.Equiv.Fin.Basic`
- `Mathlib.MeasureTheory.Constructions.Pi`
- `Mathlib.MeasureTheory.Function.LocallyIntegrable`
- `Mathlib.MeasureTheory.Function.LpSeminorm.Defs`
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
