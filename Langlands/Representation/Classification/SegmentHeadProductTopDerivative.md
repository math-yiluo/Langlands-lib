# Top derivatives of products of supplied special heads

Author: Worker 357.

This derived construction gives an actual complex-linear equivalence from
the entire top derivative of a positive-rank product of supplied special
heads to the complex scalars. It also chooses an actual irreducible
subquotient of that same product with nonzero top derivative, and actual
representation equivalences to every other such subquotient. The final
theorem is an irreducibility criterion with an explicit additional
nonvanishing hypothesis.

## Parameters and returned data

The field and original carrier universes `uF` and `uV` are independent.
The parameters are arbitrary `{p : ℕ} [Fact p.Prime]`, an actual p-adic
field `F : PadicField.{uF} p`, its supplied topological data `T`, and a
bundled continuous nontrivial unitary additive character `ψ` for that
topology. For every `n > 0`, `d : T.SegmentProductDatum.{uV,uF} n`, and
`hd : d.HasSegmentHeads`, the source is the actual induced representation
`d.induced`. The supplied blocks and their induced product have carrier
universe `max uF uV`. No resizing to the smaller universe is used.

`segmentHeadProductTopDerivativeLineEquiv` returns an actual linear
equivalence

```text
((generalLinearDerivative T ψ n n le_rfl).obj d.induced) ≃ₗ[ℂ] ℂ.
```

This concerns the full top-derivative carrier. In particular,
`segmentHeadProductTopDerivativeNontrivial` proves that this carrier is
nontrivial. There is no linkage, order, distinctness or multiplicity
restriction. Repeated segments and arbitrary ordered block families are
retained. Every block satisfies the existing strong-head relation for the
increasing segment induction. The construction does not replace that
relation by the different increasing-product segment socle.

`chooseSegmentHeadProductDetectedConstituent` returns
`ExactFunctorDetectedConstituent.Data J d.induced`, where
`J = generalLinearDerivative T ψ n n le_rfl`. Its fields are an actual
smooth representation `constituent`, its irreducibility, its actual
subquotient occurrence in `d.induced`, and nontriviality of its top
derivative. For every actual irreducible subquotient `E` of this same
product with nonzero top derivative, its `equivalence` field returns an
actual equivariant complex-linear equivalence from the chosen constituent
to `E`. It compares constituents of one ambient product. It gives no
comparison between different ambient products and no preferred or coherent
choice of equivalences.

`segmentHeadProductIsIrreducible_of_topDerivativeNonvanishing` assumes
`ExactFunctorIrreducibility.NonvanishingOnIrreducibleSubquotients J d.induced`.
This says that **every** actual irreducible subquotient of the supplied
product has nontrivial image under the actual top-derivative functor.
Under that hypothesis the theorem proves irreducibility of `d.induced`.
The hypothesis is not established here, even for unlinked segments.

## Implemented construction

For the scalar equivalence, apply the published finite-product constructor
`finiteProductTopDerivativeLineEquiv` to the exact supplied shape
`d.shape` and actual block family `d.blocks`. For block `i`, the
individual-head constructor `segmentHeadTopDerivativeLineEquiv` is applied
to `d.segments i`, `d.blocks i`, and `hd i`. These equivalences meet the
finite-product constructor's inputs without a rank transport or a change
of carrier universe in this module. Nontriviality follows from the
equivalence with the nontrivial scalar space.

The shared helper `ExactFunctorIrreducibility.preservesZero_of_exact` supplies zero-map preservation
for any functor between smooth complex representation categories in one
carrier universe that satisfies `MapsShortExactIntertwiners`. For an
object `A`, let `Z` be its actual bottom subrepresentation.
Its carrier is subsingleton. The published
`ExactFunctorIrreducibility.obj_subsingleton` shows that `J.obj Z` is also
subsingleton: exactness applied to the identity sequence on a zero object
identifies the range of its image identity with its kernel. Thus the image
of the zero map `A → Z` is zero. The zero map `A → B` factors through `Z`;
functoriality and composition with zero prove the result. This argument
adds no premise to the public derivative application.

For the detected constituent, instantiate `J` at carrier universe
`max uF uV`. The published `generalLinearDerivativeExactness` supplies
`MapsShortExactIntertwiners J`, and the private helper supplies the
zero-map-preservation instance. The scalar equivalence gives
`Module.finrank ℂ (J.obj d.induced) = 1` by transport of finrank from
`ℂ`. The published elementary dimension-one lemma gives irreducibility
of this whole image. The source has finite length by `hd.hasFiniteLength hn`.
Apply `ExactFunctorDetectedConstituent.choose` to these actual inputs.

That constructor takes a finite composition series of the source and maps
its inclusions through the exact functor. Their invariant ranges form a
zero-to-full image filtration. Exactness gives actual isomorphisms from its
grades to the images of the original simple factors. Some image grade is
nonzero, since the image object is irreducible. Choosing such a grade
gives the actual detected constituent. Any other detected irreducible
subquotient is equivalent to a factor of the same original composition
series. In an irreducible filtered image at most one grade is nonzero:
its lower step must be bottom and its upper step top, and two different
such positions contradict monotonicity. This identifies the factor
positions and gives the stored actual equivalence. No finite-length
theorem for the derivative image is needed.

The final conditional theorem applies
`ExactFunctorIrreducibility.isIrreducible_of_finrank_obj_eq_one` to the
same exact derivative, the source finite-length proof, the supplied
nonvanishing condition, and the computed dimension. For an arbitrary
subrepresentation `K` and quotient `Q` of the source, this generic proof
uses exactness of `J(K) → J(A) → J(Q)`. If `J(K)` is zero, finite length
and survival of every simple subquotient force `K = 0`. Otherwise its
injection into the irreducible image is surjective, so `J(Q)` is zero,
and the same detection argument forces `Q = 0`. It therefore controls
both subobjects and quotients. Nonzero top derivative of the source alone
does not supply the condition on all simple subquotients.

The provenance is derived composition of these existing constructors and
elementary functorial reasoning. This pair introduces no additional
literature assertion, segment derivative formula, or classification
premise.

## Publication gate and input verification

The individual-head input `fecff219-dc38-430a-a1d4-33b719d5f661` is
independently accepted and published under `lean.definition@1`. The exact
receipt reports `accepted = true`, `public = true`, independent approval
by Reviewer 8298, and publication integration
`eba5d4f32cb24fe986d4571ed0278d37` at Library
`facdf46f0abfca9e85d49d3a35285c513a96d886`. Its machine acceptance is
`d4d03d54-7c6f-41c9-ba87-fb8e809ec625`. The native, frozen and published
Lean SHA256 values are all
`50562a206452d7a9a86f9c42c15a905d1ec154fbf1aca8684364eaaeaa1b7509`;
the native, frozen and published Markdown SHA256 values are all
`5e6673fe3793d2ac8609a7391dc7411975d7c594b0a42c2bb303afab694ad9f8`.
This verification is retained in
`.private/notes/worker357-head-top-publication-verification-2026-11-02.json`.
The workspace refresh to that Library commit reports no conflicts.

The other three direct imports are unchanged published pairs in audit
Library `facdf46f0abfca9e85d49d3a35285c513a96d886`.
The individual-head input's general BZ dependency
`bfc08f82-c488-4a15-8d7f-f92c86e12803` was independently accepted and
published at `6fd0709bd33fa6c33b4d74b4b638cfc51428b8f1`, integration
`75ecdef35b4042a0ac9b0793139a7e26`. Its previously verified source pairs
remain unchanged in the present closure.

## Complete import closure and mathematical dependency audit

The recursive native audit against
`facdf46f0abfca9e85d49d3a35285c513a96d886` follows project imports after
removing nested comments and string literals. It records the direct
imports and both paired-file hashes for every project module. The
complete closure contains 1,111 project modules, including this new
module, and 297 external import roots. There are no missing modules or
missing paired Markdown files. All 1,110 inherited Lean/Markdown pairs
match the Library byte for byte, including the independently published
individual-head input verified above.

| Direct import, prefixed by `Langlands.Representation.` | Project closure, including that import | Role |
| --- | ---: | --- |
| `Classification.SegmentHeadTopDerivative` | 1,094 | Actual scalar equivalence for every supplied special head |
| `Derivative.FiniteTopLine` | 395 | Actual entire top-derivative scalar equivalence for an ordered finite product |
| `Filtration.ExactFunctorDetectedConstituent` | 95 | Actual constituent and actual equivalences within this one product |
| `Filtration.ExactFunctorIrreducibility` | 120 | Dimension-one irreducibility and the explicit conditional source criterion |

Closure sizes overlap. The complete project list and named external
roots appear in the appendices.

The inherited set is covered by four earlier inventories: the actual
individual-head construction, finite-product top line, exact-functor
detected constituent, and cuspidal-product detected constituent. Every
overlapping Lean hash agrees. The only historical Markdown hash
differences are the roots `SegmentHeadTopDerivative` and `FiniteTopLine`,
whose old inventories were made before completing their Markdown. The
former is verified against its frozen reviewed pair and the published
Library; the latter also matches the published Library. All other
inherited Markdown hashes agree.
No inherited addition lacks earlier inventory coverage.

For reproducibility, the current private inventory is
`.private/notes/worker357-head-product-top-current-import-audit-2026-11-02.json`
and its comparison report is
`.private/notes/worker357-head-product-top-comparison-2026-11-02.json`.
These private files are preparation evidence; the complete appendices
and public import graph reconstruct the module sets. This records source
coverage and proof-route inspection, without claiming that every inherited
body was newly read line by line.

The mathematical dependencies are as follows.

1. **Individual supplied heads.** The
   [individual-head audit](SegmentHeadTopDerivative.md) records its full
   1,094-module closure. An actual supercuspidal representative of the
   supplied head's base gives the published injection into decreasing
   cuspidal induction. Integral-twist freeness proves the ordered
   one-twist separation of its factors. Restrict the injection to the
   mirabolic subgroup and apply the independently proved BZ77 4.11
   theorem to its nonzero range. Transport through the actual
   source-to-range isomorphism and the restriction bridge. Admissibility
   from general cuspidal embedding and general Gelfand–Kazhdan
   multiplicity one then give the scalar equivalence. The head embedding
   itself uses individual special-constituent existence, actual
   cuspidal-induction Jacquet multiplicity and subobject/quotient
   detection, rather than a head/socle segment Jacquet formula.

2. **Finite products.** `FiniteTopLine` uses induction on the number of
   ordered positive blocks. Singleton induction is identified with its
   factor. The general first/tail induction isomorphism reduces larger
   products to a binary product. `TopProduct` specializes the proved
   general Leibniz filtration to the unique feasible top-order pair and
   uses the actual singleton-grade isomorphism. The rank-zero tensor
   comparison identifies its carrier with the full tensor product of
   the factor top-derivative carriers. Scalar equivalences in both slots
   and the tensor left unit give the binary scalar model. The carrier
   lift in first/tail regrouping stays within `max uF uV` and is
   removed by an actual equivalence in the same category. There is no
   `UniverseLiftPadic` import or arbitrary-universe derivative comparison.

3. **Exactness and finite length.** General derivative exactness follows
   from the independently proved general mirabolic-minus exactness
   results. The source-length proof embeds products of irreducible
   factors in cuspidal induction, whose length is controlled by
   geometric filtrations and a finite Jacquet detecting family.
   This uses no special-head product irreducibility or classification
   conclusion.

4. **The sixteen additions beyond the individual-head closure.**
   `Derivative.FiniteTopLine` and `TopProduct` are the general product
   constructions just described. `Filtration.SingletonIso` is
   elementary extraction of a sole actual grade. `SmoothGradedObject`,
   `ExactSmoothTransport`, `ExactSmoothSubquotients`,
   `ActualGradedExtraction` and `ExactConstituentExtraction` implement
   actual quotient objects, exact range filtrations, exact transport of
   subquotients and extraction of a nonzero image grade.
   `ExactFunctorDetectedConstituent` and `ExactFunctorIrreducibility`
   give the elementary same-filtration uniqueness and conditional
   subobject/quotient argument above. `Smooth.ConstituentSupport`
   extracts an actual simple factor from a nonzero finite-length
   representation. `FiniteLengthGrothendieck`,
   `IrreducibleCompositionFactors`, `IrreducibleGrothendieckStatement`,
   `IrreducibleGrothendieckProof` and `IrreducibleRealization` provide
   finite-length group-algebra bookkeeping, class invariance, simple
   factor realizations and actual equivalence transport. These are
   generic algebraic inputs; they add no segment derivative formula,
   head/socle Jacquet calculation, support-classification theorem, or
   irreducibility theorem for a product.

5. **The new composition.** The entire image is identified with the
   scalars before the constituent constructor is used. The actual
   source length and general exactness are discharged by published
   theorems. Survival of every simple subquotient is kept explicit
   in the conditional theorem. No step equates different products
   through their detected constituents.

## Authorized infrastructure and retained exclusions

The complete trusted operator response
[0edda6122ce65ed7ac51603c37473920](/home/taskhub/pilot/correspondence/0edda6122ce65ed7ac51603c37473920.md)
to request `d910ee3b12f2515f9568a4f2f2f1442f` permits this host to reuse
independently accepted and published BZ77 4.11, including the general
Ze80 3.7(b) comparison through the Lemma 4.7(b) closure, Ze80 5.3
`leftMixedProductHomogeneity`, and the nine generic modules listed below.
It retains all the host's independence exclusions. The individual-head
audit and the published BZ proof audit record the mathematical routes;
the new generic product and filtration additions do not extend those
permissions.


The nine modules covered by the operator's infrastructure ruling are
present with unchanged published bytes. The following table records
their contents and entry routes; none supplies an excluded conclusion.
Module prefixes are `Langlands.Representation.` except for the
combinatorial module.

| Module | Generic content and entry route |
| --- | --- |
| `Filtration.ObjectTransport` | Transport of actual filtrations along group maps and representation equivalences; reached through the mixed-product level APIs |
| `Tensor.FiniteFiltration` | Tensor-slot filtrations and their actual graded-piece equivalences; same route |
| `Tensor.ExternalFiltration` | External tensor-slot filtrations; same route |
| `Tensor.ExternalSubrepresentation` | Subrepresentations obtained from one tensor slot, with zero, top, order and properness lemmas; same route |
| `Parabolic.InductionSubrepresentation` | Actual induction of a subrepresentation and its order/properness lemmas; same route |
| `Parabolic.ProductInductionSubrepresentation` | Actual slot-induced subrepresentations of block products; same route |
| `Langlands.Combinatorics.RelationInversions` | List pair counts and inversions; reached through the Gelfand–Kazhdan Bruhat argument |
| `Derivative.MirabolicMinusNormalization` | Haar and half-modulus character identities for the general minus functors; reached through the Ze80 5.3 proof |
| `Classification.SupercuspidalDerivativesStatement` | The isolated Prop-valued BZ77 4.4 statement; its independently published proof supplies the theorem |

The first seven were introduced under socle-exhaustion task
`f3a69bc8-7312-4f82-8a7d-ea3c8188cb63`; the normalization adapter under
two-supercuspidal task `3c9849a4-a6c0-43ac-9982-d15ed76bf1e9`;
the isolated cuspidal statement under
`8e5b4563-0365-41c7-b134-70f2a0b36292`. The published BZ Markdown
identifies their introducing artifacts, project imports and owner
checks. The operator's response expressly distinguishes these generic
modules from those tasks' excluded mathematical conclusions.
The new composition uses the resulting general proof, without invoking
any of those excluded conclusions.

`Classification.Supercuspidal*` modules in the closure supply cuspidal
objects, twists, supports, duals, admissibility and independently proved
cuspidal derivatives. `Whittaker.Algebraic`, `Whittaker.GeneralLinear`
and `Whittaker.Iwasawa` supply models and functionals; their proof branch
is general Gelfand–Kazhdan multiplicity one. No Whittaker
coinvariant-finiteness statement is imported. The essential and tempered
modules supply definitions and elementary adapters, with no
square-integrable or tempered classification conclusion.

The comment-free recursive scan for both statement and theorem spellings
of the host exclusions and the additional derivative-route exclusions
has no hits. The proof routes above and the earlier independent reviews
preserve the following exclusions, including proof successors,
renamings and transitive uses:

| Excluded conclusion | Dependency check |
| --- | --- |
| Parent `GenericSegmentProductUniqueness`, task `30341ae4-65f2-4a0e-9283-763db01a409e` | No import or proof use |
| Multisegment exhaustion, task `3bfb61fa-1129-4fc9-83fd-7fcfec22106e` | No import or proof use |
| Ordered strong-head existence, task `ebea9a8a-9b21-4208-aa31-98c2dea1f8a3` | No import or proof use; the independent individual-segment existence proof is a different result |
| Quotient coverage, task `20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584` | No import or proof use |
| Ordered conversion, task `8252833d-c269-41a9-824c-5879e531b23b` | No import or proof use |
| Tempered uniqueness, task `52e97845-36bb-457d-b76f-70753334b88c` | No import or proof use |
| `SquareIntegrableLanglandsClassification`, task `1cb45da2-7007-4351-a694-594fb148b8d1` | No import or proof use |
| Square-integrable exhaustion, task `cd8ab97c-0b78-4bce-97c4-d307a28159a4` | No import or proof use |
| Regular exhaustion, task `bf433f0a-921a-428c-b0c0-6475438125ac` | No import or proof use |
| Ze80 segment derivative formulas 3.5 and 9.6, including segment-socle derivatives from `8e5b4563-0365-41c7-b134-70f2a0b36292` | No import or proof use; only the isolated proved cuspidal derivative route and authorized general comparison are used |
| Full/head/socle segment Jacquet formulas and exponent-norm formula, tasks `ed48ae06-964c-4c84-9e62-978f5a953ca7`, `55ad1e10-62d8-46b7-a081-909ef0056426`, `b95105c6-f8bb-4641-ae53-2f49d1e7f034`, `92aea10f-62ac-4e0b-bd4a-9a80909797c5` | No import or proof use; actual cuspidal Jacquet multiplicities and the authorized general derivative/Jacquet comparison are distinct inputs |
| Segment-socle product irreducibility, linked structure, gluing, commutation, swaps and socle exhaustion, including task `2ae5cbe5-0701-4509-88a0-db8cbeb35be4` | No excluded conclusion imported or used; the generic infrastructure intersections are listed above |
| The host special-head product criterion `SegmentHeadProductIrreducibility`, task `8364e73f-14ec-4d14-8f2b-1555a7c1ce95` | Neither its statement module nor a proof of it is imported; already published general constructions from this host do not assume its conclusion |
| Analytic segment classification, special square-integrability, two-supercuspidal product irreducibility or structure, and Whittaker coinvariant finiteness | No excluded conclusion imported or used |
| Unproved statements, conditional draft assemblies or pending proof tasks | No such input is used as a proof; the public BZ premise is discharged by the independently accepted published theorem |


The comment-free recursive scan finds no excluded statement/theorem name,
Lean proof hole or new axiom. Recovery check
`495dfd00-a050-4075-819e-313a8602f061` recompiled the individual-head and
product modules with zero errors and warnings. Inspection of
`segmentHeadProductTopDerivativeLineEquiv` reports independent universe
parameters `uF`, `uV` and only `propext`, `Classical.choice`, `Quot.sound`.
The earlier clean check
`02e45fbd-cd48-44e4-8053-0eceaec2f847` inspected the actual detected
constituent constructor with the same universe and axiom properties.
Compilation and this author audit do not supply independent acceptance
or publication of the new pair.

The full `SegmentHeadProductIrreducibility` criterion remains open.
This pair discharges no intermediate segment derivative/truncation bound,
no survival theorem for every simple subquotient under nonlinkage, and
no linked-pair converse or arbitrary-product permutation argument.
Neither direction of the full criterion is asserted.

## Appendix: complete project import closure

The following list includes this module and every transitive project import.

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
Langlands.Group.GL.BlockDeterminant
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
Langlands.Group.GL.MirabolicMixedOrbitCoverageProof
Langlands.Group.GL.MirabolicMixedOrbitCoverageStatement
Langlands.Group.GL.MirabolicMixedOrbitData
Langlands.Group.GL.MirabolicMixedOrbitRadicals
Langlands.Group.GL.MirabolicMixedOrbitSectionCoefficients
Langlands.Group.GL.MirabolicMixedOrbitSections
Langlands.Group.GL.MirabolicMixedOrbitSpecializations
Langlands.Group.GL.MirabolicMixedOrbitStages
Langlands.Group.GL.MirabolicMixedProductSubgroups
Langlands.Group.GL.MirabolicModularCharacterProof
Langlands.Group.GL.MirabolicModularCharacterStatement
Langlands.Group.GL.MirabolicModulusProof
Langlands.Group.GL.MirabolicModulusStatement
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
Langlands.Group.GL.ReindexCongr
Langlands.Group.GL.ReverseBlocks
Langlands.Group.GL.SingleBlock
Langlands.Group.GL.SingletonBlocks
Langlands.Group.GL.Transvection
Langlands.Group.GL.TriangularParabolic
Langlands.Group.GL.UnramifiedCharacter
Langlands.Group.GL.UpperBruhatBoundaryProof
Langlands.Group.GL.UpperBruhatBoundaryStatement
Langlands.Group.GL.UpperBruhatCells
Langlands.Group.GL.UpperBruhatCoordinatesProof
Langlands.Group.GL.UpperBruhatCoordinatesStatement
Langlands.Group.GL.UpperBruhatEmbedding
Langlands.Group.GL.UpperBruhatFiltration
Langlands.Group.GL.UpperBruhatFiltrationGeometryProof
Langlands.Group.GL.UpperBruhatFiltrationGeometryStatement
Langlands.Group.GL.UpperBruhatLocalClosednessProof
Langlands.Group.GL.UpperBruhatLocalClosednessStatement
Langlands.Group.GL.UpperBruhatPivotProof
Langlands.Group.GL.UpperBruhatPivotStatement
Langlands.Group.GL.UpperBruhatProof
Langlands.Group.GL.UpperBruhatRankProof
Langlands.Group.GL.UpperBruhatRankStatement
Langlands.Group.GL.UpperBruhatStatement
Langlands.Group.GL.UpperBruhatTransposeProof
Langlands.Group.GL.UpperBruhatTransposeStatement
Langlands.Group.GL.UpperUnipotent
Langlands.Group.GL.UpperUnipotentCompactContainmentProof
Langlands.Group.GL.UpperUnipotentCompactContainmentStatement
Langlands.Group.GL.UpperUnipotentFactorizationProof
Langlands.Group.GL.UpperUnipotentFactorizationStatement
Langlands.Group.HaarModulus
Langlands.HarmonicAnalysis.AlgebraicIntegral
Langlands.HarmonicAnalysis.AlgebraicIntegrand
Langlands.HarmonicAnalysis.Basic
Langlands.HarmonicAnalysis.CharacterTransport
Langlands.HarmonicAnalysis.Conductor
Langlands.HarmonicAnalysis.Distribution.Basic
Langlands.HarmonicAnalysis.Distribution.BruhatFiltrationVanishingProof
Langlands.HarmonicAnalysis.Distribution.BruhatFiltrationVanishingStatement
Langlands.HarmonicAnalysis.Distribution.CharacterAverage
Langlands.HarmonicAnalysis.Distribution.CharacterAverageCovarianceProof
Langlands.HarmonicAnalysis.Distribution.CharacterAverageCovarianceStatement
Langlands.HarmonicAnalysis.Distribution.CharacterAverageFactorizationProof
Langlands.HarmonicAnalysis.Distribution.CharacterAverageFactorizationStatement
Langlands.HarmonicAnalysis.Distribution.CharacterAverageSurjectiveProof
Langlands.HarmonicAnalysis.Distribution.CharacterAverageSurjectiveStatement
Langlands.HarmonicAnalysis.Distribution.ClosedRestrictionProof
Langlands.HarmonicAnalysis.Distribution.ClosedRestrictionStatement
Langlands.HarmonicAnalysis.Distribution.ClosedSupportedDescentProof
Langlands.HarmonicAnalysis.Distribution.ClosedSupportedDescentStatement
Langlands.HarmonicAnalysis.Distribution.FiniteOrbitVanishingProof
Langlands.HarmonicAnalysis.Distribution.FiniteOrbitVanishingStatement
Langlands.HarmonicAnalysis.Distribution.GeneralLinear
Langlands.HarmonicAnalysis.Distribution.HomogeneousPositivityProof
Langlands.HarmonicAnalysis.Distribution.HomogeneousPositivityStatement
Langlands.HarmonicAnalysis.Distribution.HomogeneousVanishingProof
Langlands.HarmonicAnalysis.Distribution.HomogeneousVanishingStatement
Langlands.HarmonicAnalysis.Distribution.LocalizationProof
Langlands.HarmonicAnalysis.Distribution.LocalizationStatement
Langlands.HarmonicAnalysis.Distribution.OpenRestrictionLocalityProof
Langlands.HarmonicAnalysis.Distribution.OpenRestrictionLocalityStatement
Langlands.HarmonicAnalysis.Distribution.Subspace
Langlands.HarmonicAnalysis.Distribution.SupportedDescentCovarianceProof
Langlands.HarmonicAnalysis.Distribution.SupportedDescentCovarianceStatement
Langlands.HarmonicAnalysis.Distribution.SupportedRestriction
Langlands.HarmonicAnalysis.Distribution.TransposeInvariantProof
Langlands.HarmonicAnalysis.Distribution.TransposeInvariantStatement
Langlands.HarmonicAnalysis.FiniteProductMeasureScaling
Langlands.HarmonicAnalysis.HaarConjugacy
Langlands.HarmonicAnalysis.PadicAdditiveConductorProof
Langlands.HarmonicAnalysis.PadicHaarScalingStatement
Langlands.HarmonicAnalysis.PadicLatticeTopology
Langlands.HarmonicAnalysis.PadicRectangularHaarScalingProof
Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof
Langlands.HarmonicAnalysis.RowFourier
Langlands.HarmonicAnalysis.RowSchwartzAction
Langlands.HarmonicAnalysis.RowTensorDecompositionProof
Langlands.HarmonicAnalysis.RowTensorDecompositionStatement
Langlands.HarmonicAnalysis.RowTestSmoothProof
Langlands.HarmonicAnalysis.RowTestSmoothStatement
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
Langlands.LocalFactor.Euler
Langlands.LocalFactor.Euler.Definitions
Langlands.LocalFactor.Harmonic.Statement
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
Langlands.Representation.Character.Basic
Langlands.Representation.Character.SeparationProof
Langlands.Representation.Character.SeparationStatement
Langlands.Representation.Character.TransportProof
Langlands.Representation.Character.TransportStatement
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
Langlands.Representation.Classification.CuspidalProductContragredient
Langlands.Representation.Classification.CuspidalProductDerivativeQuotientSupport
Langlands.Representation.Classification.CuspidalProductMirabolicSupportShiftProof
Langlands.Representation.Classification.CuspidalProductMirabolicSupportShiftStatement
Langlands.Representation.Classification.Essential
Langlands.Representation.Classification.HeadQuotientCriterionProof
Langlands.Representation.Classification.HeadQuotientCriterionStatement
Langlands.Representation.Classification.IrreducibleProductEmbedding
Langlands.Representation.Classification.IrreducibleProductEmbeddingStatement
Langlands.Representation.Classification.IrreducibleProductFiniteLengthProof
Langlands.Representation.Classification.LanglandsData
Langlands.Representation.Classification.MirabolicDerivativeContragredient
Langlands.Representation.Classification.MultiplicityOneConstituentProof
Langlands.Representation.Classification.MultiplicityOneConstituentStatement
Langlands.Representation.Classification.NormalizedProductFiniteLengthStatement
Langlands.Representation.Classification.OppositeCuspidalJacquetFiltrationProof
Langlands.Representation.Classification.OppositeCuspidalJacquetFiltrationStatement
Langlands.Representation.Classification.OppositeJacquetQuotientDetectionProof
Langlands.Representation.Classification.OppositeJacquetQuotientDetectionStatement
Langlands.Representation.Classification.OppositeJacquetReciprocity
Langlands.Representation.Classification.OppositeSupportJacquetAdapter
Langlands.Representation.Classification.SegmentConstituentStatement
Langlands.Representation.Classification.SegmentDecreasingCuspidalProduct
Langlands.Representation.Classification.SegmentHeadDecreasingSocle
Langlands.Representation.Classification.SegmentHeadProductFiniteness
Langlands.Representation.Classification.SegmentHeadProductTopDerivative
Langlands.Representation.Classification.SegmentHeadTopDerivative
Langlands.Representation.Classification.SegmentInductionAdmissibilityProof
Langlands.Representation.Classification.SegmentInductionAdmissibilityStatement
Langlands.Representation.Classification.SegmentJacquetMultiplicityProof
Langlands.Representation.Classification.SegmentJacquetMultiplicityStatement
Langlands.Representation.Classification.SegmentJacquetReversal
Langlands.Representation.Classification.SegmentSpecialConstituentExistenceProof
Langlands.Representation.Classification.SegmentTensorReversalProof
Langlands.Representation.Classification.SegmentTensorReversalStatement
Langlands.Representation.Classification.SegmentTensorStabilizerProof
Langlands.Representation.Classification.SegmentTensorStabilizerStatement
Langlands.Representation.Classification.Segments
Langlands.Representation.Classification.Supercuspidal
Langlands.Representation.Classification.SupercuspidalContragredient
Langlands.Representation.Classification.SupercuspidalContragredientAux
Langlands.Representation.Classification.SupercuspidalContragredientProof
Langlands.Representation.Classification.SupercuspidalContragredientStatement
Langlands.Representation.Classification.SupercuspidalDerivativeVanishing
Langlands.Representation.Classification.SupercuspidalDerivativesProof
Langlands.Representation.Classification.SupercuspidalDerivativesStatement
Langlands.Representation.Classification.SupercuspidalSupport
Langlands.Representation.Classification.SupercuspidalSupportStatement
Langlands.Representation.Classification.SupercuspidalSupportUniquenessProof
Langlands.Representation.Classification.SupercuspidalTopDerivative
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
Langlands.Representation.CuspidalSupport.AssociationReverseProof
Langlands.Representation.CuspidalSupport.AssociationReverseStatement
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
Langlands.Representation.CuspidalSupport.WholeLeviTransport
Langlands.Representation.CuspidalSupport.ZeroRankEmbeddingProof
Langlands.Representation.Derivative.FiniteTopLine
Langlands.Representation.Derivative.GeneralLinearDerivativeExactnessProof
Langlands.Representation.Derivative.GeneralLinearDerivativeExactnessStatement
Langlands.Representation.Derivative.GeneralLinearDerivativeLeibnizBoundary
Langlands.Representation.Derivative.GeneralLinearDerivativeLeibnizFiltrationProof
Langlands.Representation.Derivative.GeneralLinearDerivativeLeibnizFiltrationStatement
Langlands.Representation.Derivative.Homogeneity
Langlands.Representation.Derivative.Iteration
Langlands.Representation.Derivative.LeftMixedProductDerivativeProof
Langlands.Representation.Derivative.LeftMixedProductHigher
Langlands.Representation.Derivative.LeftMixedProductHomogeneityProof
Langlands.Representation.Derivative.LeftMixedProductHomogeneityStatement
Langlands.Representation.Derivative.LeftMixedProductPhiHatIterate
Langlands.Representation.Derivative.LeftMixedProductVanishing
Langlands.Representation.Derivative.LeftMixedProductZeroRank
Langlands.Representation.Derivative.LeibnizIndices
Langlands.Representation.Derivative.LeibnizPieceCompat
Langlands.Representation.Derivative.LeibnizPositiveGluing
Langlands.Representation.Derivative.LeibnizQuotientPiece
Langlands.Representation.Derivative.LeibnizRankZeroBoundary
Langlands.Representation.Derivative.LeibnizRankZeroGluing
Langlands.Representation.Derivative.LeibnizRestrictionCompat
Langlands.Representation.Derivative.LeibnizRestrictionExact
Langlands.Representation.Derivative.LeibnizZeroFirstPiece
Langlands.Representation.Derivative.LevelCalculus
Langlands.Representation.Derivative.MinusVanishing
Langlands.Representation.Derivative.MirabolicCharacter
Langlands.Representation.Derivative.MirabolicDerivativeDetectionProof
Langlands.Representation.Derivative.MirabolicDerivativeDetectionStatement
Langlands.Representation.Derivative.MirabolicDerivativeUnitInjective
Langlands.Representation.Derivative.MirabolicDerivativeVanishing
Langlands.Representation.Derivative.MirabolicDeterminant
Langlands.Representation.Derivative.MirabolicHighestDerivativeDescent
Langlands.Representation.Derivative.MirabolicHighestDerivativePairingProof
Langlands.Representation.Derivative.MirabolicHighestDerivativePairingStatement
Langlands.Representation.Derivative.MirabolicLatticeBox
Langlands.Representation.Derivative.MirabolicMinus
Langlands.Representation.Derivative.MirabolicMinusExactnessProof
Langlands.Representation.Derivative.MirabolicMinusExactnessStatement
Langlands.Representation.Derivative.MirabolicMinusNormalization
Langlands.Representation.Derivative.MirabolicMinusPairingTransferProof
Langlands.Representation.Derivative.MirabolicMinusPairingTransferStatement
Langlands.Representation.Derivative.MirabolicMixedOrbitCharacters
Langlands.Representation.Derivative.MirabolicPhiMinusMackey
Langlands.Representation.Derivative.MirabolicPhiMinusNondegeneratePairing
Langlands.Representation.Derivative.MirabolicPlus
Langlands.Representation.Derivative.MirabolicPlusNormalization
Langlands.Representation.Derivative.MirabolicProductMinusBoundary
Langlands.Representation.Derivative.MirabolicProductMinusCompatibility
Langlands.Representation.Derivative.MirabolicProductMinusCompatibilityStatement
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhi
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiCoefficient
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiCompactComparison
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiHaar
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiHostTransport
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiIdentityComparison
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiInductionNormalization
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiLocalization
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiMackeyLocalization
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiNormalization
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiNormalizedSection
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiSection
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiSourceAction
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiSourceComparison
Langlands.Representation.Derivative.MirabolicProductMinusLeftPhiStagesComparison
Langlands.Representation.Derivative.MirabolicProductMinusLeftPsi
Langlands.Representation.Derivative.MirabolicProductMinusLeftPsiInduction
Langlands.Representation.Derivative.MirabolicProductMinusPhiKernelComparison
Langlands.Representation.Derivative.MirabolicProductMinusRightBoundary
Langlands.Representation.Derivative.MirabolicProductMinusRightPhi
Langlands.Representation.Derivative.MirabolicProductMinusRightPhiAssembly
Langlands.Representation.Derivative.MirabolicProductMinusRightPhiCycle
Langlands.Representation.Derivative.MirabolicProductMinusRightPhiCycleCoefficient
Langlands.Representation.Derivative.MirabolicProductMinusRightPhiCycleGroups
Langlands.Representation.Derivative.MirabolicProductMinusRightPhiIdentity
Langlands.Representation.Derivative.MirabolicProductMinusRightPhiIdentityCoefficient
Langlands.Representation.Derivative.MirabolicProductMinusRightPhiIdentityGroups
Langlands.Representation.Derivative.MirabolicProductMinusRightPsi
Langlands.Representation.Derivative.MirabolicProductMinusRightPsiCoefficient
Langlands.Representation.Derivative.MirabolicProductMinusRightPsiGroups
Langlands.Representation.Derivative.MirabolicProductMinusRightPsiZero
Langlands.Representation.Derivative.MirabolicProductRestriction
Langlands.Representation.Derivative.MirabolicProductRestrictionCasts
Langlands.Representation.Derivative.MirabolicProductRestrictionFactors
Langlands.Representation.Derivative.MirabolicProductRestrictionMackey
Langlands.Representation.Derivative.MirabolicProductRestrictionOrbits
Langlands.Representation.Derivative.MirabolicProductRestrictionStabilizers
Langlands.Representation.Derivative.MirabolicProductRestrictionStatement
Langlands.Representation.Derivative.MirabolicProductRestrictionTransport
Langlands.Representation.Derivative.MirabolicSmoothPhiPlus
Langlands.Representation.Derivative.MirabolicSmoothPhiPlusAdjunction
Langlands.Representation.Derivative.MirabolicSmoothPhiPlusIterate
Langlands.Representation.Derivative.MirabolicSmoothPhiPlusProduct
Langlands.Representation.Derivative.MixedProductDerivativeStatement
Langlands.Representation.Derivative.MixedProductRankCast
Langlands.Representation.Derivative.OrderRecursion
Langlands.Representation.Derivative.OrderedCuspidalProductHeadShift
Langlands.Representation.Derivative.OrderedCuspidalProductNondegeneracyProof
Langlands.Representation.Derivative.OrderedCuspidalProductNondegeneracyStatement
Langlands.Representation.Derivative.OrderedCuspidalProductTwistOne
Langlands.Representation.Derivative.Partial
Langlands.Representation.Derivative.PartialDerivativeJacquetComparisonProof
Langlands.Representation.Derivative.PartialDerivativeJacquetComparisonStatement
Langlands.Representation.Derivative.PartialDerivativeJacquetLHS
Langlands.Representation.Derivative.PartialDerivativeJacquetNormalization
Langlands.Representation.Derivative.PartialDerivativeJacquetRHS
Langlands.Representation.Derivative.PartialDerivativeJacquetRHSComparison
Langlands.Representation.Derivative.PartialLocalizationCharacter
Langlands.Representation.Derivative.PartialLocalizationData
Langlands.Representation.Derivative.ProductVanishing
Langlands.Representation.Derivative.RankCastCompat
Langlands.Representation.Derivative.RestrictedProductLevel
Langlands.Representation.Derivative.RestrictionBridge
Langlands.Representation.Derivative.RightMixedLevel
Langlands.Representation.Derivative.RightMixedProductDerivativeFiltrationProof
Langlands.Representation.Derivative.RightMixedProductDerivativeFiltrationStatement
Langlands.Representation.Derivative.RightMixedProductDerivativePositive
Langlands.Representation.Derivative.RightMixedProductPhiMinusDetectionProof
Langlands.Representation.Derivative.RightMixedProductZeroRank
Langlands.Representation.Derivative.ShortExactFunctorLaws
Langlands.Representation.Derivative.TopLine
Langlands.Representation.Derivative.TopLocalizationData
Langlands.Representation.Derivative.TopProduct
Langlands.Representation.Derivative.ZeroRankTensor
Langlands.Representation.Dual.Definitions
Langlands.Representation.Exponents.Central
Langlands.Representation.Exponents.DualJacquet
Langlands.Representation.Exponents.DualJacquetStatement
Langlands.Representation.Exponents.Jacquet
Langlands.Representation.Exponents.NilpotenceIndex
Langlands.Representation.Exponents.ParabolicPair
Langlands.Representation.Exponents.UnitaryDualJacquetSupportAdapters
Langlands.Representation.Filtration.ActualGradedExtraction
Langlands.Representation.Filtration.CoinvariantVanishingStatement
Langlands.Representation.Filtration.CommonSubquotientStatement
Langlands.Representation.Filtration.Definitions
Langlands.Representation.Filtration.ExactConstituentExtraction
Langlands.Representation.Filtration.ExactFunctorDetectedConstituent
Langlands.Representation.Filtration.ExactFunctorIrreducibility
Langlands.Representation.Filtration.ExactSmoothSubquotients
Langlands.Representation.Filtration.ExactSmoothTransport
Langlands.Representation.Filtration.FiniteFamilyMultiplicityProof
Langlands.Representation.Filtration.FiniteFamilyMultiplicityStatement
Langlands.Representation.Filtration.GluedFamily
Langlands.Representation.Filtration.GradedRefinementProof
Langlands.Representation.Filtration.GradedRefinementStatement
Langlands.Representation.Filtration.IntervalLiftProof
Langlands.Representation.Filtration.IntervalLiftStatement
Langlands.Representation.Filtration.InvariantBilinear
Langlands.Representation.Filtration.InvariantBilinearBounds
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
Langlands.Representation.Filtration.NonzeroHomCommonSubquotientProof
Langlands.Representation.Filtration.NonzeroHomCommonSubquotientStatement
Langlands.Representation.Filtration.ObjectDefinitions
Langlands.Representation.Filtration.ObjectTransport
Langlands.Representation.Filtration.OneStep
Langlands.Representation.Filtration.Precomposition
Langlands.Representation.Filtration.QuasicuspidalVanishingProof
Langlands.Representation.Filtration.QuotientFirstIso
Langlands.Representation.Filtration.QuotientTail
Langlands.Representation.Filtration.RepresentationLength
Langlands.Representation.Filtration.SimpleMapMultiplicityDetectionProof
Langlands.Representation.Filtration.SimpleMapMultiplicityDetectionStatement
Langlands.Representation.Filtration.SimpleSubquotientFactorProof
Langlands.Representation.Filtration.SimpleSubquotientFactorStatement
Langlands.Representation.Filtration.SingletonIso
Langlands.Representation.Filtration.SmoothGradedObject
Langlands.Representation.Filtration.Splicing
Langlands.Representation.Filtration.Splicing.Basic
Langlands.Representation.Filtration.SubquotientAlgebraProof
Langlands.Representation.Filtration.SubquotientAlgebraStatement
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
Langlands.Representation.Hecke.ActionLocalUnits
Langlands.Representation.Hecke.ActionProjection
Langlands.Representation.Hecke.AntiPullback
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
Langlands.Representation.Induction.BinaryPositiveCompact
Langlands.Representation.Induction.BinaryProduct
Langlands.Representation.Induction.BlockCharacterAbsorption
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
Langlands.Representation.Induction.SplitKernelCharacter
Langlands.Representation.Induction.SplitKernelCharacterExtension
Langlands.Representation.Induction.SplitKernelCompact
Langlands.Representation.Induction.SplitKernelCovariance
Langlands.Representation.Induction.SplitKernelEquivariant
Langlands.Representation.Induction.SplitKernelHaarTrivial
Langlands.Representation.Induction.SplitKernelIntegral
Langlands.Representation.Induction.SplitKernelLocalizationData
Langlands.Representation.Induction.SplitKernelSectionAction
Langlands.Representation.Induction.SplitQuotientProof
Langlands.Representation.Induction.SplitQuotientStatement
Langlands.Representation.Induction.SplitStagesCharacterComparison
Langlands.Representation.Induction.SplitStagesCharacterComparisonStatement
Langlands.Representation.Induction.SplitStagesCharacterIntegrand
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
Langlands.Representation.Jacquet.CharacterAveraging
Langlands.Representation.Jacquet.CharacterTwistEquiv
Langlands.Representation.Jacquet.Coinvariants
Langlands.Representation.Jacquet.CompactCompressionStableDualityProof
Langlands.Representation.Jacquet.CompactCompressionStableDualityStatement
Langlands.Representation.Jacquet.CompressionStabilizationProof
Langlands.Representation.Jacquet.CompressionStabilizationStatement
Langlands.Representation.Jacquet.ExactProof
Langlands.Representation.Jacquet.ExactStatement
Langlands.Representation.Jacquet.Localization
Langlands.Representation.Jacquet.LocalizationExactnessProof
Langlands.Representation.Jacquet.LocalizationExactnessStatement
Langlands.Representation.Jacquet.LocalizationTower
Langlands.Representation.Jacquet.LocalizationTransport
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
Langlands.Representation.Mirabolic.LeftMixedProductSuccessor
Langlands.Representation.Mirabolic.MixedProducts
Langlands.Representation.OrbitSpan
Langlands.Representation.Parabolic.AdmissibilityStatement
Langlands.Representation.Parabolic.ComposedFunctors
Langlands.Representation.Parabolic.FlattenedRefinementModulusCalculation
Langlands.Representation.Parabolic.GeometricPrerequisitesStatement
Langlands.Representation.Parabolic.HeadTailProductInduction
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
Langlands.Representation.RankinSelberg.AnalyticStatement
Langlands.Representation.RankinSelberg.EqualRankFrobeniusProof
Langlands.Representation.RankinSelberg.EqualRankFrobeniusStatement
Langlands.Representation.RankinSelberg.EqualRankTrilinearAssembly
Langlands.Representation.RankinSelberg.EqualRankTrilinearReduction
Langlands.Representation.RankinSelberg.EqualRankTrilinearUniquenessStatement
Langlands.Representation.RankinSelberg.FunctionalEquationStatement
Langlands.Representation.RankinSelberg.GeneralLinearUnimodularity
Langlands.Representation.RankinSelberg.HaarSymmetriesProof
Langlands.Representation.RankinSelberg.HaarSymmetriesStatement
Langlands.Representation.RankinSelberg.LastRowCompactOrbitProof
Langlands.Representation.RankinSelberg.LastRowCompactOrbitStatement
Langlands.Representation.RankinSelberg.LocalFactor
Langlands.Representation.RankinSelberg.Measures
Langlands.Representation.RankinSelberg.QuotientIntegrals
Langlands.Representation.RankinSelberg.RankOneQuotient
Langlands.Representation.RankinSelberg.RationalContinuation
Langlands.Representation.RankinSelberg.RationalZeta
Langlands.Representation.RankinSelberg.TwistInvariance
Langlands.Representation.RankinSelberg.UnimodularityStatement
Langlands.Representation.RankinSelberg.UnipotentQuotient
Langlands.Representation.RankinSelberg.UnipotentUnimodularity
Langlands.Representation.RankinSelberg.ZeroRowLastRowCutoffProof
Langlands.Representation.RankinSelberg.ZeroRowLastRowCutoffStatement
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
Langlands.Representation.Smooth.ConstituentSupport
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
Langlands.Representation.Smooth.IrreducibleCompositionFactors
Langlands.Representation.Smooth.IrreducibleGrothendieckProof
Langlands.Representation.Smooth.IrreducibleGrothendieckStatement
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
Langlands.Representation.Tensor.Filtration
Langlands.Representation.Tensor.Finite
Langlands.Representation.Tensor.FiniteEquivalences
Langlands.Representation.Tensor.FiniteFiltration
Langlands.Representation.Tensor.FiniteProperties
Langlands.Representation.Tensor.FiniteRegrouping
Langlands.Representation.Tensor.FlattenedGLRefinement
Langlands.Representation.Tensor.GLRefinement
Langlands.Representation.Tensor.OneFactor
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
Langlands.Representation.Whittaker.AlgebraicTwist
Langlands.Representation.Whittaker.BruhatCellDistribution
Langlands.Representation.Whittaker.BruhatCellFactorizationProof
Langlands.Representation.Whittaker.BruhatCellFactorizationStatement
Langlands.Representation.Whittaker.BruhatCellInvarianceProof
Langlands.Representation.Whittaker.BruhatCellInvarianceStatement
Langlands.Representation.Whittaker.BruhatCellRestrictionVanishingProof
Langlands.Representation.Whittaker.BruhatCellRestrictionVanishingStatement
Langlands.Representation.Whittaker.BruhatCellVanishingProof
Langlands.Representation.Whittaker.BruhatCellVanishingStatement
Langlands.Representation.Whittaker.BruhatCompatibleSupportProof
Langlands.Representation.Whittaker.BruhatCompatibleSupportStatement
Langlands.Representation.Whittaker.BruhatFiberAverage
Langlands.Representation.Whittaker.BruhatFiberCharacterCovarianceProof
Langlands.Representation.Whittaker.BruhatFiberCharacterCovarianceStatement
Langlands.Representation.Whittaker.BruhatHaarMeasureProof
Langlands.Representation.Whittaker.BruhatHaarMeasureStatement
Langlands.Representation.Whittaker.BruhatOrbitalIntegrationProof
Langlands.Representation.Whittaker.BruhatOrbitalIntegrationStatement
Langlands.Representation.Whittaker.BundledDualTransport
Langlands.Representation.Whittaker.CharacterChange
Langlands.Representation.Whittaker.CoefficientDistribution
Langlands.Representation.Whittaker.CompatibleMonomialFixedProof
Langlands.Representation.Whittaker.CompatibleMonomialFixedStatement
Langlands.Representation.Whittaker.CompatibleTorus
Langlands.Representation.Whittaker.Distribution
Langlands.Representation.Whittaker.DistributionInvarianceProof
Langlands.Representation.Whittaker.DistributionInvarianceStatement
Langlands.Representation.Whittaker.DualTransform
Langlands.Representation.Whittaker.EntrywiseCharacter
Langlands.Representation.Whittaker.GeneralLinear
Langlands.Representation.Whittaker.GeneralizedCoefficient
Langlands.Representation.Whittaker.GeneralizedCoefficientDescent
Langlands.Representation.Whittaker.GeneralizedCoefficientKernelProof
Langlands.Representation.Whittaker.GeneralizedCoefficientKernelStatement
Langlands.Representation.Whittaker.GeneralizedCoefficientSeparation
Langlands.Representation.Whittaker.GenericDualTransport
Langlands.Representation.Whittaker.Iwasawa
Langlands.Representation.Whittaker.MirabolicQuotientMeasure
Langlands.Representation.Whittaker.MultiplicityOneProof
Langlands.Representation.Whittaker.MultiplicityOneStatement
Langlands.Representation.Whittaker.PrerequisiteInterfaces
Langlands.Representation.Whittaker.PrerequisitesStatement
Langlands.Representation.Whittaker.Twist
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

## Appendix: external import roots

These are the distinct nonproject roots encountered by the recursive traversal.

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
Mathlib.Algebra.Group.Action.Hom
Mathlib.Algebra.Group.Action.Opposite
Mathlib.Algebra.Group.AddChar
Mathlib.Algebra.Group.Equiv.TypeTags
Mathlib.Algebra.Group.Hom.Instances
Mathlib.Algebra.Group.Pi.Lemmas
Mathlib.Algebra.Group.Subgroup.Ker
Mathlib.Algebra.Group.Subgroup.Pointwise
Mathlib.Algebra.Group.Submonoid.Basic
Mathlib.Algebra.Group.TypeTags.Finite
Mathlib.Algebra.Group.TypeTags.Hom
Mathlib.Algebra.Module.LinearMap.FiniteRange
Mathlib.Algebra.Module.Opposite
Mathlib.Algebra.Module.PID
Mathlib.Algebra.Module.Projective
Mathlib.Algebra.Module.Submodule.Map
Mathlib.Algebra.Module.ULift
Mathlib.Algebra.Order.Archimedean.Basic
Mathlib.Algebra.Order.BigOperators.Group.Finset
Mathlib.Algebra.Polynomial.FieldDivision
Mathlib.Algebra.Polynomial.Laurent
Mathlib.Algebra.Polynomial.Lifts
Mathlib.Algebra.Polynomial.Module.AEval
Mathlib.Algebra.Polynomial.Module.FiniteDimensional
Mathlib.Algebra.Polynomial.Roots
Mathlib.Algebra.Ring.GeomSum
Mathlib.Analysis.Complex.Basic
Mathlib.Analysis.Complex.Cardinality
Mathlib.Analysis.Complex.Circle
Mathlib.Analysis.Complex.Polynomial.Basic
Mathlib.Analysis.Fourier.FourierTransform
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
Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
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
Mathlib.Data.Fin.Tuple.Basic
Mathlib.Data.Fin.Tuple.Sort
Mathlib.Data.Finset.NatAntidiagonal
Mathlib.Data.Fintype.EquivFin
Mathlib.Data.Fintype.Quotient
Mathlib.Data.Fintype.Sort
Mathlib.Data.Fintype.Sum
Mathlib.Data.Int.Cast.Lemmas
Mathlib.Data.Int.Interval
Mathlib.Data.Int.LeastGreatest
Mathlib.Data.List.Pairwise
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
Mathlib.LinearAlgebra.AnnihilatingPolynomial
Mathlib.LinearAlgebra.Basis.VectorSpace
Mathlib.LinearAlgebra.BilinearForm.Properties
Mathlib.LinearAlgebra.BilinearMap
Mathlib.LinearAlgebra.Charpoly.Basic
Mathlib.LinearAlgebra.Charpoly.ToMatrix
Mathlib.LinearAlgebra.Determinant
Mathlib.LinearAlgebra.Dimension.Basic
Mathlib.LinearAlgebra.Dimension.Constructions
Mathlib.LinearAlgebra.Dimension.StrongRankCondition
Mathlib.LinearAlgebra.DirectSum.Finite
Mathlib.LinearAlgebra.Dual.Defs
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
Mathlib.LinearAlgebra.Matrix.BilinearForm
Mathlib.LinearAlgebra.Matrix.Block
Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
Mathlib.LinearAlgebra.Matrix.Charpoly.Univ
Mathlib.LinearAlgebra.Matrix.Diagonal
Mathlib.LinearAlgebra.Matrix.ElementaryRowOperations
Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
Mathlib.LinearAlgebra.Matrix.Kronecker
Mathlib.LinearAlgebra.Matrix.NonsingularInverse
Mathlib.LinearAlgebra.Matrix.Permutation
Mathlib.LinearAlgebra.Matrix.Rank
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
Mathlib.MeasureTheory.Group.MeasurableEquiv
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
Mathlib.MeasureTheory.Measure.Prod
Mathlib.MeasureTheory.Measure.Regular
Mathlib.MeasureTheory.Measure.Typeclasses.Finite
Mathlib.NumberTheory.LocalField.Basic
Mathlib.NumberTheory.Padics.LocalField
Mathlib.NumberTheory.Padics.RingHoms
Mathlib.Order.Atoms
Mathlib.Order.CompactlyGenerated.Basic
Mathlib.Order.Hom.Set
Mathlib.Order.Interval.Finset.Fin
Mathlib.Order.Interval.Set.Infinite
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
Mathlib.RingTheory.Flat.Basic
Mathlib.RingTheory.FractionalIdeal.Operations
Mathlib.RingTheory.Ideal.Quotient.Basic
Mathlib.RingTheory.Ideal.Quotient.Operations
Mathlib.RingTheory.Jacobson.Semiprimary
Mathlib.RingTheory.Length
Mathlib.RingTheory.Localization.Ideal
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
Mathlib.RingTheory.Trace.Basic
Mathlib.RingTheory.Valuation.Extension
Mathlib.RingTheory.Valuation.Integral
Mathlib.RingTheory.Valuation.LocalSubring
Mathlib.RingTheory.Valuation.RamificationGroup
Mathlib.Tactic
Mathlib.Tactic.Group
Mathlib.Tactic.Linarith
Mathlib.Tactic.LinearCombination
Mathlib.Tactic.NoncommRing
Mathlib.Tactic.NormNum
Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
Mathlib.Topology.Algebra.ClopenNhdofOne
Mathlib.Topology.Algebra.ConstMulAction
Mathlib.Topology.Algebra.Constructions
Mathlib.Topology.Algebra.ContinuousMonoidHom
Mathlib.Topology.Algebra.Field
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
Mathlib.Topology.Homeomorph.Defs
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
