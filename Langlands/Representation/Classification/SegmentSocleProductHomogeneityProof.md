# Zelevinsky 6.2: homogeneity of endpoint-separated segment-socle products

Module `Langlands.Representation.Classification.SegmentSocleProductHomogeneityProof`,
namespace `Langlands.Classification`.

The theorem `Langlands.Classification.segmentSocleProductHomogeneity` proves
the unchanged published proposition
`Langlands.Classification.SegmentSocleProductHomogeneity.{uF,uV} F T` from
`Langlands.Representation.Classification.SegmentSocleProductHomogeneityStatement`.
It is the only declaration of the module.

## Statement

The outer telescope is
`{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)`.
The result is exactly `SegmentSocleProductHomogeneity.{uF, uV} F T`: for every
supplied `ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology`,
every `N : ℕ` and every `d : T.SegmentProductDatum.{uV, uF} (N + 1)`, if
`d.HasSegmentSocles` and

```lean
∀ i j : Fin d.length, i < j → (d.segments j).base ≠ ((d.segments i).last).twist 1
```

then `Derivative.IsGeneralLinearHomogeneous T ψ d.induced`.

This is Zelevinsky's Theorem 6.2: for segments `Δ_i = [ρ_i, ρ'_i]` with
`ρ_j ≠ ν ρ'_i` whenever `i < j`, the product `⟨Δ_1⟩ × ⋯ × ⟨Δ_r⟩` is
homogeneous. Homogeneity is the published
`Derivative.IsGeneralLinearHomogeneous`: every nonbottom invariant subspace of
the actual mirabolic restriction of `d.induced` has the same derivative level
as the whole restriction.

The theorem keeps the target as published. It covers every positive rank
`N + 1`, including `N = 0` (`GL_1` restricted to `P_1`). It quantifies over
every datum, so every supplied block, multiplicity and segment order is
covered, with the actual normalized product `d.induced` and right translation.
The endpoint condition is used only in its published direction
(earlier last member, later base, real exponent `1`). The theorem has no
hypothesis beyond the telescope: no finite length, admissibility,
nonlinkage, nonzeroness, derivative, filtration or normalization assumption.
The target makes no rank-zero assertion, and none is added. The field universe
`uF` and the segment-base universe `uV` are independent, and the product
carriers live in `Type (max uF uV)`, as in the statement.

## Implemented proof

The proof is one term:

```lean
segmentSocleProductHomogeneity_of T
  (Mirabolic.minusExactness.{uF, max uF uV} F T)
  (MirabolicProductMinus.rightPhiShortExact.{uF, max uF uV} (F := F) T)
  (MirabolicProductMinus.rightPhiBoundary.{uF, max uF uV} (F := F) T)
  (rightMixedProductPhiMinusDetection.{uF, max uF uV} F T)
  (leftMixedProductDerivative.{uF, max uF uV} F T)
  (leftMixedProductHomogeneity.{uF, max uF uV} F T)
  (segmentSocleDerivatives.{uF, uV} F T)
  (segmentSocleProductHighestDerivative.{uF, uV} F T)
  (cuspidalProductMirabolicSupportShift.{uF, uV} F T)
```

`segmentSocleProductHomogeneity_of` (published module
`Classification.SegmentSocleProductHomogeneityAssembly`) proves the target from nine lower
propositions, taken as explicit hypotheses `hE hS hB hD hLD hH h35 hF hC`.
Each of the nine now has a published proof, and the term supplies these
proofs in that order (table below). Nothing else is needed: the proof does not
unfold the target, and it introduces no local lemma.

Universes. The representations in the target live in `Type (max uF uV)`. So
the six propositions about mirabolic and mixed products (`hE`, `hS`, `hB`,
`hD`, `hLD`, `hH`) are instantiated at `uF, max uF uV`. The three segment
propositions (`h35`, `hF`, `hC`) already place their representations in
`Type (max uF uV)`; they are instantiated at `uF, uV`. These are exactly the
universes at which `segmentSocleProductHomogeneity_of` takes its hypotheses.
The published proofs of `hS` and `hB` take `F` implicitly, hence `(F := F)`.

### The proof route of the assembly

The mathematics is in the published modules below, which formalize Ze80
§6.3, the argument of BZ77 4.15 adapted to segments. Their Markdown files give
the details.

- `Classification.SegmentSocleProductHomogeneityInduction`
  (`homogeneous_of_caseTwo`):
  induction on the number of segments. With one segment, Ze80 3.5 (`h35`)
  shows that the only nonzero derivative of positive order of `⟨Δ⟩` is the one
  of order `Δ.rank`, which gives homogeneity. In the step,
  `d.induced ≅ ⟨Δ_1⟩ × π°`, and the tail `π°` is homogeneous by induction.
  BZ77 4.13(a)–(c) (published `mirabolicProductRestriction`, `hS`, `hB`) give
  the short exact sequence `0 → σ → π|P → τ → 0` of the restriction of
  `π = ⟨Δ_1⟩ × π°` to `P`. The subrepresentation `σ`
  (`restrictionSubobject`) is the right mixed product, and the quotient
  `τ = ⟨Δ_1⟩ × (π°|P)` (`restrictionQuotient`) is the left mixed product.
  A nonzero invariant subspace `ω` of `π|P` either meets `σ` (Case 1), or has
  zero intersection with `σ`, so that `ω` injects into `τ` (Case 2). Case 1 is
  handled with BZ77 4.13(d) (`hD`), 4.14(a) (`hLD`), Ze80 5.3 (`hH`) and the
  exactness of `Φ⁻` (`hE`), in `Derivative.RightMixedLevel` and
  `Derivative.RestrictedProductLevel`. Case 2 enters the induction as the
  premise `CaseTwoExclusion`: no nontrivial representation `W` of the
  mirabolic group has both an injective intertwiner into the whole
  restriction `π|P` (`restrictedProduct`, not `σ`) and an injective
  intertwiner into `τ`.
- `Classification.SegmentSocleProductCaseTwo` (`caseTwoExclusion`): Case 2
  cannot occur, that is, `CaseTwoExclusion` holds whenever
  `π°|P` is homogeneous. Let `W ≠ 0` inject into `π|P` and into `τ`, and let
  `λ°` be the level of the homogeneous `π°|P`. By Ze80 5.3 (`hH`), `τ` is
  homogeneous of level `λ°`, so `W` has level `λ°`. By the exactness of `Φ⁻`
  (`hE`), the highest derivative `W^(λ°)` of `W` embeds into
  `τ^(λ°) ≅ ⟨Δ_1⟩ × π°^(λ°)` (BZ77 4.14(a), `hLD`), and the
  highest-derivative calculation `hF` gives
  `π°^(λ°) ≅ ⟨Δ_2⁻⟩ × ⋯ × ⟨Δ_r⁻⟩`. So an irreducible subrepresentation of
  `W^(λ°)` has cuspidal support `Δ_1 + Δ_2⁻ + ⋯ + Δ_r⁻` (each segment read as
  the multiset of its members). Since `W` also embeds into `π|P`, and `π`
  embeds into a product of supercuspidal representations with support
  `Δ_1 + ⋯ + Δ_r`, BZ77 4.7(b) in mirabolic form (`hC`), applied to that
  irreducible subrepresentation of `W^(λ°)`, gives
  `ν · (Δ_1 + Δ_2⁻ + ⋯ + Δ_r⁻) ≤ Δ_1 + ⋯ + Δ_r` as multisets of cuspidal
  data. `SegmentContentShift.not_map_twist_le` refutes this using the
  endpoint condition and the published `cuspidalIntegralTwistFreeness`
  (`ρ ν^k ≅ ρ` only for `k = 0`). This is Zelevinsky's "reasoning of 4.5"
  (Ze80 6.3(3)), applied in Case 2 of BZ77 4.15.

## Published proof inputs

Every input is a published proof. Module names are
under `Langlands.Representation`. All are unchanged in the base `41034879`
used here.

| Hypothesis | Theorem (module) | Source |
| --- | --- | --- |
| target | `Classification.SegmentSocleProductHomogeneity` (`Classification.SegmentSocleProductHomogeneityStatement`) | Ze80 6.2 |
| assembly | `Classification.segmentSocleProductHomogeneity_of` (`Classification.SegmentSocleProductHomogeneityAssembly`) | Ze80 6.3 |
| `hE` | `Derivative.Mirabolic.minusExactness` (`Derivative.MirabolicMinusExactnessProof`) | exactness of `Ψ⁻`, `Φ⁻` (BZ77 3.2) |
| `hS` | `Derivative.MirabolicProductMinus.rightPhiShortExact` (`Derivative.MirabolicProductMinusRightPhi`) | BZ77 4.13(c) |
| `hB` | `Derivative.MirabolicProductMinus.rightPhiBoundary` (`Derivative.MirabolicProductMinusRightBoundary`) | BZ77 4.13(c), `P_1` boundary |
| `hD` | `Derivative.rightMixedProductPhiMinusDetection` (`Derivative.RightMixedProductPhiMinusDetectionProof`) | BZ77 4.13(d) |
| `hLD` | `Derivative.leftMixedProductDerivative` (`Derivative.LeftMixedProductDerivativeProof`) | BZ77 4.14(a) |
| `hH` | `Derivative.leftMixedProductHomogeneity` (`Derivative.LeftMixedProductHomogeneityProof`) | Ze80 5.3 |
| `h35` | `Classification.segmentSocleDerivatives` (`Classification.SegmentSocleDerivativesProof`) | Ze80 3.5 |
| `hF` | `Classification.segmentSocleProductHighestDerivative` (`Classification.SegmentSocleProductHighestDerivativeProof`) | highest derivative of a segment-socle product (Ze80 3.5, BZ77 4.6) |
| `hC` | `Classification.cuspidalProductMirabolicSupportShift` (`Classification.CuspidalProductMirabolicSupportShiftProof`) | BZ77 4.7(b), as used in Ze80 4.4–4.5 |

BZ77 4.13(a) is not a hypothesis of the assembly. The assembly uses the
published proof `Derivative.mirabolicProductRestriction` (module
`Derivative.MirabolicProductRestriction`).

The proof of `hE` (`Derivative.MirabolicMinusExactnessProof`) is imported as
published and used unchanged. This module does not prove, replace or bypass it.

## Normalization and sources

The derivative, the mirabolic functors and the normalized products are the
published ones, with their determinant normalization at exponent `-1/2`. This
module and the assembly make no comparison between that normalization and a
Haar modulus. Such comparisons occur only inside published inputs. They rest on
the published `Group.GL.MirabolicModulusProof`, as recorded in the
Markdown of `hF` and `h35`. No new normalization assertion is assumed.

Registered originals (read at the cited pages):

- A. V. Zelevinsky, *Induced representations of reductive p-adic groups II.
  On irreducible representations of GL(n)* (1980), literature ID
  `zelevinsky-1980-induced-ii`, SHA256
  `663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
  Theorem 6.2 is on printed p.188; its proof 6.3 is on printed pp.188–189;
  §§5.1–5.3 (mixed products, homogeneity, Proposition 5.3) are on printed
  pp.187–188. In the supplied PDF, printed page `x` is one-based PDF page
  `x − 163`, so these are PDF pp.24–26.
- I. N. Bernstein and A. V. Zelevinsky, *Induced representations of reductive
  p-adic groups I* (1977), literature ID `bernstein-zelevinsky-1977-induced-i`,
  SHA256 `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
  4.11–4.14 (restriction of products to `P`, mixed products, their
  derivatives) and the proof 4.15 are on printed pp.456–459, one-based PDF
  pp.17–20 (printed page `x` is PDF page `x − 439`).

No applicable erratum is registered in the literature index or the public
notes. The citations explain the provenance of the route; the published Lean
inputs above are the proofs used.

## Import audit

### Direct imports

The module imports the assembly and the modules of the nine proofs, all under
`Langlands.Representation`: `Classification.SegmentSocleProductHomogeneityAssembly`,
`Derivative.LeftMixedProductDerivativeProof`,
`Derivative.LeftMixedProductHomogeneityProof`,
`Derivative.MirabolicMinusExactnessProof`,
`Derivative.MirabolicProductMinusRightBoundary`,
`Derivative.MirabolicProductMinusRightPhi`,
`Derivative.RightMixedProductPhiMinusDetectionProof`,
`Classification.CuspidalProductMirabolicSupportShiftProof`,
`Classification.SegmentSocleDerivativesProof` and
`Classification.SegmentSocleProductHighestDerivativeProof`.

### Closure

The audit follows every `Langlands` import recursively, including imports used
only for definitions or by unused neighbouring declarations. It was run against
Library commit `4103487976e26033768519d7c8e53adf6d10c898`.

- The transitive project import closure has 1,227 modules: this module and
  1,226 published modules. The copies of all 1,226 Lean and Markdown
  files checked here are byte-identical to that commit. Every closure module has a nonempty
  paired Markdown file.
- The closure has 316 external import roots, all from Lean core and Mathlib.
- The closure is the union of the closures of the direct imports and this
  module. Their sizes: assembly 606, `hE` 68, `hS` 257, `hB` 145, `hD` 103,
  `hLD` 261, `hH` 314, `h35` 1,178, `hF` 1,202, `hC` 607; the target statement
  has 81.
- The target statement's closure is unchanged and contains no classification
  definition module listed in the tables below.

Closure modules by top-level namespace (relative to `Langlands`; total 1,227):

| Namespace | Modules | Namespace | Modules |
| --- | --- | --- | --- |
| `Representation.Classification` | 134 | `Representation.Hecke` | 18 |
| `Representation.Derivative` | 126 | `Representation.Category` | 13 |
| `Representation.CuspidalSupport` | 112 | `Representation.Unitary` | 13 |
| `Group` | 97 | `LinearAlgebra` | 12 |
| `Representation.Geometric` | 73 | `ClassFieldTheory` | 10 |
| `Representation.Induction` | 72 | `Algebra` | 9 |
| `Representation.Parabolic` | 67 | `Galois` | 9 |
| `Representation.Filtration` | 57 | `LocalField` | 9 |
| `HarmonicAnalysis` | 54 | `Representation.Compact` | 7 |
| `Representation.Smooth` | 51 | `Representation.Exponents` | 7 |
| `Representation.Whittaker` | 45 | `Representation.MatrixCoefficient` | 7 |
| `Representation.Jacquet` | 40 | `Topology` | 7 |
| `Representation.RankinSelberg` | 24 | `Correspondence` | 6 |
| `Weil` | 24 | `Representation.Shahidi` | 6 |
| `Representation.Tensor` | 23 | `WeilDeligne` | 6 |
| `Representation.CompactCoefficient` | 22 | `Representation.Character` | 5 |
| `Representation.Twist` | 19 | `Representation.Conductor` | 5 |
| `Analysis` | 18 | `Representation.Unramified` | 5 |
| `LocalFactor` | 4 | `VirtualRepresentation` | 3 |
| `Representation.Mirabolic` | 2 | `Representation.Schur` | 2 |
| `Combinatorics` | 1 | `Representation.Dual` | 1 |
| `Representation.OrbitSpan` | 1 | `Representation.SubrepresentationLattice` | 1 |

Twenty-two closure modules were not published as a statement, proof or
definition of their own. One is this module. Eighteen are the relocated infrastructure modules listed in the
Markdown of `h35` (`Group.GL.{BlockScalarCenter, OneBlockShape, RankReindex,
ReindexCongr, Transvection}`, `HarmonicAnalysis.{FiniteProductMeasureScaling,
PadicLatticeTopology}`, `Representation.Compact.OrbitMeanTranslation`,
`Representation.CuspidalSupport.WholeLeviTransport`,
`Representation.Derivative.{MirabolicDeterminant, ShortExactFunctorLaws}`,
`Representation.Geometric.CoarseLeviReversal`, `Representation.OrbitSpan`,
`Representation.Parabolic.{InducedMapSurjectivity, OppositeJacquetMap}`,
`Representation.Smooth.Transfer.GroupEquivalence`,
`Representation.Tensor.OneFactor`, `Topology.CompactNormCharacter`). The other
three were also relocated in the Library without changing declarations:
`Group.LeftQuotient` (generic left cosets, from `Induction.Definitions` and the
quotient-measure modules), `Algebra.MultisetOfFn` (one multiset identity) and
`Classification.SegmentProductCuspidalMembers` (ordered cuspidal members of a
segment product). The last two come from the published
`SegmentProductCuspidalEmbedding`.

### Modules beyond the closure of `hF`

The closure of `hF` (1,202 modules) is audited in its own Markdown, which
contains the closure of `h35` (1,178 modules, audited in the Markdown of `h35`).
The complete difference is the following 25 modules. All except this module are
published; names are relative to `Langlands.Representation` unless they begin
with `Langlands.`.

| Module | Content |
| --- | --- |
| `Langlands.Algebra.MultisetOfFn` | multiset of `List.ofFn` as a sum of singletons |
| `Classification.IrreducibleProductFiniteLengthProof` | finite length of products of irreducibles |
| `Classification.SegmentContentShift` | cuspidal content of a segment and its shift; `not_map_twist_le` |
| `Classification.SegmentCuspidalContent` | definition of the cuspidal content of a multisegment |
| `Classification.SegmentProductCuspidalEmbedding` | embedding of a segment-socle product into a cuspidal product |
| `Classification.SegmentProductCuspidalMembers` | ordered cuspidal members of a segment product |
| `Classification.SegmentSocleProductCaseTwo` | Case 2 of Ze80 6.3 |
| `Classification.SegmentSocleProductHomogeneityAssembly` | the conditional assembly |
| `Classification.SegmentSocleProductHomogeneityInduction` | the induction on the number of segments |
| `Classification.SegmentSocleProductHomogeneityProof` | this module |
| `Classification.SegmentSocleProductHomogeneityStatement` | the target |
| `Derivative.LeftMixedProductHomogeneityProof` | Ze80 5.3 |
| `Derivative.LeftMixedProductHomogeneityStatement` | Ze80 5.3 statement |
| `Derivative.LeftMixedProductPhiHatIterate` | left mixed product and iterated `Φ̂⁺` |
| `Derivative.MirabolicDerivativeUnitInjective` | injectivity of the derivative unit |
| `Derivative.MirabolicMinusNormalization` | normalization of `Ψ⁻` |
| `Derivative.MirabolicPlusNormalization` | normalization of `Φ⁺` |
| `Derivative.MirabolicSmoothPhiPlus` | smooth induction `Φ̂⁺` (BZ77 1.8) |
| `Derivative.MirabolicSmoothPhiPlusAdjunction` | `Φ⁻ ⊣ Φ̂⁺` |
| `Derivative.MirabolicSmoothPhiPlusIterate` | iterated adjunction |
| `Derivative.MirabolicSmoothPhiPlusProduct` | left `Φ̂⁺` embedding of products |
| `Derivative.RestrictedProductLevel` | Case 1 and the case split |
| `Derivative.RestrictionBridge` | GL restriction and mirabolic levels |
| `Derivative.RightMixedLevel` | levels of right mixed products |
| `Derivative.RightMixedProductPhiMinusDetectionProof` | BZ77 4.13(d) |

These are mixed-product and mirabolic infrastructure, the Ze80 5.3 and BZ77
4.13(d) proofs, the published helper and assembly modules of this proof, and one
general finite-length theorem. None proves a classification, exhaustion,
irreducibility criterion or linked-pair result. Removing also the closures of
`h35`, `hF` and the assembly leaves only this module and the `hH`/`hD` modules
`LeftMixedProductHomogeneityProof`, `LeftMixedProductPhiHatIterate`,
`MirabolicDerivativeUnitInjective`, `MirabolicMinusNormalization`,
`MirabolicPlusNormalization`, `MirabolicSmoothPhiPlus{,Adjunction,Iterate,Product}`
and `RightMixedProductPhiMinusDetectionProof`.

## Independence audit

### Excluded results with modules in the closure

For every published proof with a module in the closure (its main module or
a listed file), the result it proves was compared with the 18 exclusions of
this proof, with
`AdjacentUnlinkedSegmentSocleSwap` and `TwoSegmentSocleCommutation`, with the
linked-pair results (`LinkedSegmentSocleReverseProductStructure`,
`LinkedSegmentSoclePairReducible`, `JuxtaposedSegmentSocleReverseProductStructure`
and `LinkedSegmentSocleReverseProductQuotientHom` with their proofs,
`LinkedSegmentSocleGluing`), with the later statements (c), (d), (e) of
`SegmentSocleDerivativesStatement`, and with the nonadjacent-consumer
exclusions listed below. Among the 18 exclusions of this proof, the only one
hit is ordered special-segment conversion: its module
`Classification.SegmentProductPermutation` (a definition module, also an
auxiliary file of the proof of that result) is in the statement chain of
`h35`/`hF`, and no declaration of it is used (below). No proof of a
linked-pair, swap, commutation or later statement has a module in the
closure. The remaining hits are nonadjacent-consumer exclusions, treated in
the next subsection.

Definition modules are not tied to a proof in this comparison. The generic
definition modules that belong to excluded results are those of the
following table, as already audited in the Markdown of `h35` and `hF`.
Declaration counts are from the declaration audit below.

| Module (under `Langlands.Representation`, except `Combinatorics`) | Belongs to | How reached | Declarations used |
| --- | --- | --- | --- |
| `Classification.TrivialGroupQuotient` | quotient coverage | statement chain of `h35`/`hF` | 0 |
| `Classification.SegmentProductPermutation` | ordered special-segment conversion | statement chain of `h35`/`hF` | 0 |
| `Classification.OrderedMultisegmentHeadReduction` | ordered special-head existence | statement chain of `h35`/`hF` | 0 |
| `Classification.SegmentSocleProductData` | socle exhaustion | statement chain of `h35`/`hF` | 0 |
| `Classification.SingletonSegmentSocle` | socle exhaustion | statement chain of `h35`/`hF` | 19: rank casts `castRank`, `castRankEquiv`, `isIrreducible_castRank`, `normalizedProductRankCastIso`, and `singletonSegmentInducedEquiv` (with their auxiliary proofs) |
| `Combinatorics.RelationInversions` | socle exhaustion | inside `h35` | 6: `relationInversions`, `relationPairCount` and equation lemmas |
| `Filtration.ObjectTransport` | socle exhaustion | inside the assembly, `hH`, `h35`, `hF` | 13: `ObjectRepFiltration.comp`, `compGradedEquiv`, `equivTransportGradedEquiv` |
| `Tensor.FiniteFiltration` | socle exhaustion | inside the assembly, `hH`, `hF` | 4: `FiniteTensor.slotEquiv`, auxiliary proofs of `FiniteTensor.congrEquiv` |
| `Filtration.SingletonIso` | special-head product criterion | inside `hF` | 7: `RepFunctorFiltration.lengthOneGradedIso` |
| `Induction.EmptyProductUnit` | special-head product criterion | inside `hF` | 14: empty-product evaluation and unit isomorphisms |
| `Classification.CuspidalProductDerivativeQuotientSupport` | support-shift theorem (c) | inside `h35`, `hF`, `hC` | 57: quotient form of BZ77 4.7(a) inside the BZ77 4.7(b) proof |
| `Classification.RegularLanglandsHeadReduction` | regular exhaustion (definition module) | inside `h35` | 1: generic `RegularHeadExistence.nontrivial_normalizedProductInduction` |

The statement chain of `h35`/`hF` also reaches the statement module
`Classification.MultisegmentClassificationStatement`. It names
`OrderedMultisegmentSocleExistence` and `SquareIntegrableLanglandsClassification`
only as proposition definitions; no declaration of it is used. The statement
modules `OrderedSegmentSquareIntegrableConversionStatement`,
`RegularLanglandsStatement` and `TemperedBlockStatement` are in the closure,
and none of their declarations is used either. As recorded in the Markdown of
`h35` and `hF`, such generic infrastructure is distinguished from the excluded
conclusions, and the BZ77 4.7(b) closure is used.

### Detection and the nonadjacent-consumer restrictions

The general detection result and its nonadjacent-product consumer
(`Classification.TwoSupercuspidalNonadjacentIrreducibilityProof`) come with
restrictions on what may be used. They bind detection, its prerequisites and
that consumer, and do not prohibit the separately specified Ze80 5.4/6.2
arguments in their respective consumers. Ze80 6.3 uses Ze80 3.5 as an input.

- The general detection result is `Derivative.MirabolicDerivativeDetectionProof`
  (`mirabolicDerivativeDetection`). It is
  used, through the assembly, `h35`, `hC`, `hD`, `hF` and `hH`. Its closure
  has 78 modules: no segment, socle or Jacquet-formula module, and no module
  that belongs to an excluded result. So the detection restrictions hold.
- The nonadjacent-product proof has a closure of
  657 modules. Its only segment module is `Classification.Segments`; its only
  module that belongs to a nonadjacent-consumer exclusion is the generic
  `Classification.CuspidalIntegralTwistFreenessProof`.
- The modules of results named in the nonadjacent-consumer list enter this closure
  only through `h35` (Ze80 3.5) and `hF`, which imports `h35`:
  the proofs of `segmentSocleJacquetFormula` (with
  `SegmentSocleJacquetReduction`), `segmentFullJacquetFormula`,
  `segmentZelevinskyConstituentExistence`, the two-supercuspidal structure,
  the nonadjacent irreducibility (with `TwoSupercuspidalDerivativeBridge` and
  `NonadjacentAssembly`), and the modules
  `CommonImageMultiplicityOneProof`, `CuspidalJacquetFunctorExactnessProof`,
  `MultiplicityOneConstituentProof`, `SegmentInductionAdmissibilityProof`,
  `SegmentJacquetMultiplicityProof`, `SegmentTensorReversalProof`,
  `SegmentTensorStabilizerProof`, `UpperJacquetSubrepresentationDetectionProof`,
  `CuspidalSupport.DistinctTensorStabilizerProof` and
  `Filtration.SimpleMapMultiplicityDetectionProof`. The Markdown of `h35`
  audits these inputs.
- One exception: `Classification.CuspidalIntegralTwistFreenessProof`
  (published together with the modules just listed) is also used directly, by
  `SegmentSocleProductCaseTwo`. Its theorem `cuspidalIntegralTwistFreeness`
  says only that `ρ ν^k ≅ ρ` forces `k = 0` for a supercuspidal `ρ`
  (central-character argument). It contains no special-head or reverse-socle
  existence result.
- No module of the analytic segment classification, of the forward
  special-segment essential square-integrability, or of three further results
  of the nonadjacent-consumer list is in the closure.

### Declaration audit

A development check (`run_cmd` in a separate file importing this module, not
part of the Library) collected every constant reachable from
`Langlands.Classification.segmentSocleProductHomogeneity` through
`getUsedConstantsAsSet`, transitively through the values and types of all
constants. Results:

- 92,910 constants are reachable; 14,904 of them are in 1,027 `Langlands`
  modules.
- No reachable constant has a name component equal to any of 47 excluded
  names or their lower-camel forms. The names are
  `OrderedMultisegmentSocleExistence`, `MultisegmentSocleExhaustion`,
  `MultisegmentSocleExistence`, `SegmentEssentialSquareIntegrableClassification`,
  `SegmentSquareIntegrabilityTheorems`, `PadicSegmentSquareIntegrabilityTheorems`,
  `UnlinkedSegmentSocleProductIrreducible`, `SegmentSocleProductIrreducibility`,
  `AdjacentUnlinkedSegmentSocleSwap`, `AdjacentUnlinkedSegmentSwap`,
  `TwoSegmentSocleCommutation`, `TwoSegmentHeadCommutation`,
  `SegmentHeadProductIrreducibility`, `MultisegmentHeadExhaustion`,
  `OrderedMultisegmentHeadExistence`, `MultisegmentHeadExistence`,
  `TemperedLanglandsQuotientCoverage`, `OrderedMultisegmentQuotientExhaustion`,
  `ZeroRankMultisegmentQuotientExhaustion`, `TemperedBlockUniqueness`,
  `TemperedBlockExhaustion`, `SquareIntegrableLanglandsClassification`,
  `SquareIntegrableLanglandsExhaustion`, `SquareIntegrableLanglandsHeadExistence`,
  `SquareIntegrableLanglandsQuotientUniqueness`,
  `GLRegularLanglandsExhaustionStatement`, `GenericSegmentProductUniqueness`,
  `GenericSegmentProductExhaustion`, `OrderedSegmentSquareIntegrableConversion`,
  `SegmentSpecialEssentialSquareIntegrability`,
  `SegmentCenteredSpecialSquareIntegrability`,
  `SegmentSpecialSquareIntegrabilityCriterion`, `MultisegmentSocleClassification`,
  `OrderedMultisegmentSocleClassification`, `MultisegmentHeadClassification`,
  `OrderedMultisegmentHeadClassification`, `MultisegmentClassificationTheorems`,
  `PadicMultisegmentClassificationTheorems`, `LinkedSegmentSoclePairReducible`,
  `LinkedSegmentSocleReverseProductStructure`,
  `LinkedSegmentSocleReverseProductQuotientHom`,
  `JuxtaposedSegmentSocleReverseProductStructure`, `LinkedSegmentSocleGluing`,
  `HighestDerivativeSupportShift`, `SquareIntegrableSegmentNonlinkage`,
  `OrderedIntegralSegmentInductionSquareIntegrableCollapse` and
  `IncreasingAdjacentQuotientUpperProductIrreducibility`.
- Used declarations of the modules in the tables above are as listed there.
  From `Classification.SegmentSocleDerivativesStatement` only the two
  propositions `SegmentSocleDerivatives` and
  `SegmentSocleProductHighestDerivative` are reachable (with their auxiliary
  proofs), the statements of `h35` and `hF`.
- The used theorems of the nonadjacent-list modules are
  `segmentSocleJacquetFormula`, `segmentFullJacquetFormula`,
  `segmentZelevinskyConstituentExistence`, `twoSupercuspidalProductStructure`,
  `twoSupercuspidalNonadjacentProductIrreducible` and
  `cuspidalIntegralTwistFreeness` (and the generic lemmas of the
  multiplicity-one modules listed above), all inside `h35` except the last, as
  stated above.

### Exclusion table

| Exclusion of this proof (conclusion, its proofs, transitive dependencies) | Result |
| --- | --- |
| Ordered-socle existence (`OrderedMultisegmentSocleExistence`) | No proof dependency; the name occurs only as a proposition definition in `MultisegmentClassificationStatement`, and no declaration of it is used. This proof is a lower input of ordered-socle existence; no module of the closure consumes the target. |
| Socle exhaustion | Only the generic definition modules in the table above. |
| Analytic segment classification | Absent. |
| Segment-socle product irreducibility | Absent. |
| Final segment-socle irreducibility criterion | Absent. |
| `AdjacentUnlinkedSegmentSocleSwap` | Absent. |
| `TwoSegmentSocleCommutation` | Absent. |
| Special-head product criterion | Only the generic `SingletonIso` and `EmptyProductUnit` (inside `hF`). |
| Special-head exhaustion | Absent. |
| Ordered special-head existence | Only the definition module `OrderedMultisegmentHeadReduction` (statement chain of `h35`/`hF`, no declaration used). |
| Quotient coverage | Only the definition module `TrivialGroupQuotient` (statement chain, no declaration used). |
| Tempered block uniqueness | Absent; the statement module `TemperedBlockStatement` is present with no declaration used. |
| `SquareIntegrableLanglandsClassification` | Absent, except the proposition-definition name in `MultisegmentClassificationStatement`. |
| Square-integrable exhaustion | Absent. |
| Regular exhaustion | Absent; from `RegularLanglandsHeadReduction` only the generic nontriviality lemma above. |
| `GenericSegmentProductUniqueness` | Absent. |
| Ordered special-segment conversion | Only the definition module `SegmentProductPermutation` (statement chain, no declaration used); the statement module `OrderedSegmentSquareIntegrableConversionStatement` is present with no declaration used. |
| Forward special-segment essential square-integrability | Absent. |
| Ze80 6.1(a) and later, linked-pair results, final product criteria, classification | Absent: no linked-pair, gluing, reverse-product or classification theorem is reachable. |

This audit checks mathematical dependencies. A generic module that belongs to
an excluded result is not treated as use of that result's conclusion, and a
statement definition or citation is not treated as a proof.

## Validation

The Lean source has SHA256
`84e9e12d67f1356a20d90bda6fc3188fc60ee91d534bd4be819eef919246a29c`.
`lean_check` (at Library
commit `41034879`) built the module with zero errors and zero warnings. Inspection of
`Langlands.Classification.segmentSocleProductHomogeneity` reports universe
parameters `uF`, `uV` and only the axioms `propext`, `Classical.choice` and
`Quot.sound`. The file contains no `sorry`, `admit` or new axiom.

The module only applies published theorems by name.
