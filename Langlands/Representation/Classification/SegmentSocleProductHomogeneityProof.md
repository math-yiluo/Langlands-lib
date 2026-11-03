# Zelevinsky 6.2: homogeneity of endpoint-separated segment-socle products

Author: Worker 1070. Task: `b711af72-fdf9-4b32-a450-937911426822`, revision 1.

Module `Langlands.Representation.Classification.SegmentSocleProductHomogeneityProof`,
namespace `Langlands.Classification`.

The theorem `Langlands.Classification.segmentSocleProductHomogeneity` proves
the unchanged published proposition
`Langlands.Classification.SegmentSocleProductHomogeneity.{uF,uV} F T` from
`Langlands.Representation.Classification.SegmentSocleProductHomogeneityStatement`
(statement artifact `67f113f2-8b01-4004-ac08-c37879d759dc`, authored by
Workers 700 and 999). It is the only declaration of the module.

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
`Classification.SegmentSocleProductHomogeneityAssembly`, artifact
`54e7626d-0319-42a7-bb1e-01a603b6458a`) proves the target from nine lower
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

The mathematics is in published modules of this task, which formalize Ze80
§6.3, the argument of BZ77 4.15 adapted to segments. Their Markdown files give
the details.

- `Classification.SegmentSocleProductHomogeneityInduction`
  (`homogeneous_of_caseTwo`, artifact `b006f56e-c499-4ae3-945e-a842aa52ef74`):
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
- `Classification.SegmentSocleProductCaseTwo` (`caseTwoExclusion`, same
  artifact): Case 2 cannot occur, that is, `CaseTwoExclusion` holds whenever
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

Every input is an independently accepted, published proof. Module names are
under `Langlands.Representation`. "Commit" is the Library commit of the first
publication; all are unchanged in the base `41034879` used here.

| Hypothesis | Theorem (module) | Source | Artifact / task / commit / integration |
| --- | --- | --- | --- |
| target | `Classification.SegmentSocleProductHomogeneity` (`Classification.SegmentSocleProductHomogeneityStatement`) | Ze80 6.2 | statement `67f113f2-8b01-4004-ac08-c37879d759dc` / `819a0526` / `64f062d4` / `5f4fd3ec`, Reviewer 4644 |
| assembly | `Classification.segmentSocleProductHomogeneity_of` (`Classification.SegmentSocleProductHomogeneityAssembly`) | Ze80 6.3 | `54e7626d-0319-42a7-bb1e-01a603b6458a` / `b711af72` / `8bffffb6` / `a51e493f` |
| `hE` | `Derivative.Mirabolic.minusExactness` (`Derivative.MirabolicMinusExactnessProof`) | exactness of `Ψ⁻`, `Φ⁻` (BZ77 3.2) | `d307cd07-7e0f-4e38-a3d5-94b78bb3a7d6` / `b65bc667` / `9a8ca758` / `d20a668c` |
| `hS` | `Derivative.MirabolicProductMinus.rightPhiShortExact` (`Derivative.MirabolicProductMinusRightPhi`) | BZ77 4.13(c) | `5449db58-f9bb-4e02-a2a2-96b83f3984ba` / `6cd54f76` / `00315d47` / `9e1415c1` |
| `hB` | `Derivative.MirabolicProductMinus.rightPhiBoundary` (`Derivative.MirabolicProductMinusRightBoundary`) | BZ77 4.13(c), `P_1` boundary | `58a3c341-c399-4caa-ba3c-d78fc5619b90` / `6cd54f76` / `b22e1857` / `59d5e1e9` |
| `hD` | `Derivative.rightMixedProductPhiMinusDetection` (`Derivative.RightMixedProductPhiMinusDetectionProof`) | BZ77 4.13(d) | `a07ed51f-f4b9-447c-9da8-cecaed53a506` / `f8acf579` / `9a8ca758` / `d12107eb` |
| `hLD` | `Derivative.leftMixedProductDerivative` (`Derivative.LeftMixedProductDerivativeProof`) | BZ77 4.14(a) | `e99bbe1b-06fe-42ad-b8ec-d1c4e02c9929` / `7e19f753` / `b4b4160d` / `553698f2` |
| `hH` | `Derivative.leftMixedProductHomogeneity` (`Derivative.LeftMixedProductHomogeneityProof`) | Ze80 5.3 | `e183909c-e3a3-4843-b1b4-dd3700a47c37` / `6bb62ea4` (r2) / `da0312e3` / `baae4a1f` |
| `h35` | `Classification.segmentSocleDerivatives` (`Classification.SegmentSocleDerivativesProof`) | Ze80 3.5 | `ac220f41-e7d4-4c9f-951f-0ff12e51412f` / `209027ca` / `e530d1eb` / `b202a6bd` |
| `hF` | `Classification.segmentSocleProductHighestDerivative` (`Classification.SegmentSocleProductHighestDerivativeProof`) | highest derivative of a segment-socle product (Ze80 3.5, BZ77 4.6) | `cf12542e-ed32-4ef1-b46d-48e47a342d5e` / `4e152d19` / `286dd3b7` / `6c5cb54e` |
| `hC` | `Classification.cuspidalProductMirabolicSupportShift` (`Classification.CuspidalProductMirabolicSupportShiftProof`) | BZ77 4.7(b), as used in Ze80 4.4–4.5 | `4b8c7a7c-baaf-4fb3-bb60-213389f02470` / `0b3bf4c1` / `9a8ca758` / `19323125` |

BZ77 4.13(a) is not a hypothesis of the assembly. The assembly uses the
published proof `Derivative.mirabolicProductRestriction` (module
`Derivative.MirabolicProductRestriction`, task `a1d00661`).

The proof of `hE` belongs to task `b65bc667-6951-4bd5-82af-10fb7046df7f`,
which is under user controls. It is imported only after its publication and is
used unchanged. This task did not prove, replace or bypass it.

## Normalization and sources

The derivative, the mirabolic functors and the normalized products are the
published ones, with their determinant normalization at exponent `-1/2`. This
module and the assembly make no comparison between that normalization and a
Haar modulus. Such comparisons occur only inside published inputs. They rest on
the independently published `Group.GL.MirabolicModulusProof` (artifact
`f25fdd6c-d842-40be-b220-92bda8715865`, task `f947a735`), as recorded in the
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
  1,226 published modules. The workspace copies of all 1,226 Lean and Markdown
  files are byte-identical to that commit. Every closure module has a nonempty
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

Twenty-two closure modules have no artifact manifest of their own. One is this
module. Eighteen are the relocated infrastructure modules listed in the
Markdown of `h35` (`Group.GL.{BlockScalarCenter, OneBlockShape, RankReindex,
ReindexCongr, Transvection}`, `HarmonicAnalysis.{FiniteProductMeasureScaling,
PadicLatticeTopology}`, `Representation.Compact.OrbitMeanTranslation`,
`Representation.CuspidalSupport.WholeLeviTransport`,
`Representation.Derivative.{MirabolicDeterminant, ShortExactFunctorLaws}`,
`Representation.Geometric.CoarseLeviReversal`, `Representation.OrbitSpan`,
`Representation.Parabolic.{InducedMapSurjectivity, OppositeJacquetMap}`,
`Representation.Smooth.Transfer.GroupEquivalence`,
`Representation.Tensor.OneFactor`, `Topology.CompactNormCharacter`). The other
three were also relocated by the Integrator without changing declarations:
`Group.LeftQuotient` (generic left cosets, from `Induction.Definitions` and the
quotient-measure modules), `Algebra.MultisetOfFn` (one multiset identity) and
`Classification.SegmentProductCuspidalMembers` (ordered cuspidal members of a
segment product). The last two come from this task's published
`SegmentProductCuspidalEmbedding`.

### Modules beyond the closure of `hF`

The closure of `hF` (1,202 modules) is audited in its own Markdown, which
contains the closure of `h35` (1,178 modules, audited in the Markdown of `h35`).
The complete difference is the following 25 modules. All except this module are
published; names are relative to `Langlands.Representation` unless they begin
with `Langlands.`.

| Module | Content | Origin (artifact / task) |
| --- | --- | --- |
| `Langlands.Algebra.MultisetOfFn` | multiset of `List.ofFn` as a sum of singletons | relocated from `5440c02b` |
| `Classification.IrreducibleProductFiniteLengthProof` | finite length of products of irreducibles | `41a8585c` / `0717fd42` |
| `Classification.SegmentContentShift` | cuspidal content of a segment and its shift; `not_map_twist_le` | `5440c02b` (this task) |
| `Classification.SegmentCuspidalContent` | definition of the cuspidal content of a multisegment | `09d34c08` (definition) |
| `Classification.SegmentProductCuspidalEmbedding` | embedding of a segment-socle product into a cuspidal product | `5440c02b` (this task) |
| `Classification.SegmentProductCuspidalMembers` | ordered cuspidal members of a segment product | relocated from `5440c02b` |
| `Classification.SegmentSocleProductCaseTwo` | Case 2 of Ze80 6.3 | `b006f56e` (this task) |
| `Classification.SegmentSocleProductHomogeneityAssembly` | the conditional assembly | `54e7626d` (this task) |
| `Classification.SegmentSocleProductHomogeneityInduction` | the induction on the number of segments | `b006f56e` (this task) |
| `Classification.SegmentSocleProductHomogeneityProof` | this module | this candidate |
| `Classification.SegmentSocleProductHomogeneityStatement` | the target | `67f113f2` / `819a0526` |
| `Derivative.LeftMixedProductHomogeneityProof` | Ze80 5.3 | `e183909c` / `6bb62ea4` |
| `Derivative.LeftMixedProductHomogeneityStatement` | Ze80 5.3 statement | `1e101502` (statement) |
| `Derivative.LeftMixedProductPhiHatIterate` | left mixed product and iterated `Φ̂⁺` | `ac76e357` (definition) |
| `Derivative.MirabolicDerivativeUnitInjective` | injectivity of the derivative unit | `bab82164` (definition) |
| `Derivative.MirabolicMinusNormalization` | normalization of `Ψ⁻` | `149ed2a1` (definition) |
| `Derivative.MirabolicPlusNormalization` | normalization of `Φ⁺` | `cc091205` (definition) |
| `Derivative.MirabolicSmoothPhiPlus` | smooth induction `Φ̂⁺` (BZ77 1.8) | `2546568e` (definition) |
| `Derivative.MirabolicSmoothPhiPlusAdjunction` | `Φ⁻ ⊣ Φ̂⁺` | `567eec05` (definition) |
| `Derivative.MirabolicSmoothPhiPlusIterate` | iterated adjunction | `2a7f2b35` (definition) |
| `Derivative.MirabolicSmoothPhiPlusProduct` | left `Φ̂⁺` embedding of products | `ea098c88` (definition) |
| `Derivative.RestrictedProductLevel` | Case 1 and the case split | `6ded142e` (this task) |
| `Derivative.RestrictionBridge` | GL restriction and mirabolic levels | `6ded142e` (this task) |
| `Derivative.RightMixedLevel` | levels of right mixed products | `6ded142e` (this task) |
| `Derivative.RightMixedProductPhiMinusDetectionProof` | BZ77 4.13(d) | `a07ed51f` / `f8acf579` |

These are mixed-product and mirabolic infrastructure, the Ze80 5.3 and BZ77
4.13(d) proofs, this task's published helper and assembly modules, and one
general finite-length theorem. None proves a classification, exhaustion,
irreducibility criterion or linked-pair result. Removing also the closures of
`h35`, `hF` and the assembly leaves only this module and the `hH`/`hD` modules
`LeftMixedProductHomogeneityProof`, `LeftMixedProductPhiHatIterate`,
`MirabolicDerivativeUnitInjective`, `MirabolicMinusNormalization`,
`MirabolicPlusNormalization`, `MirabolicSmoothPhiPlus{,Adjunction,Iterate,Product}`
and `RightMixedProductPhiMinusDetectionProof`.

## Independence audit

### Owners of closure modules

For every published artifact whose entry module or listed repository path lies
in the closure, its owning task was compared with the 18 exclusions of this
task, the related tasks `e3634665`, `cded83f3` (`AdjacentUnlinkedSegmentSocleSwap`),
`426911b4`, `66e3b87c` (`TwoSegmentSocleCommutation`), the linked-pair tasks
`a55c4267`, `8fa9f68b`, `7ff2a1e9` (with successors `0c90f7e4`, `ba6ec030`),
`c84cd52c`, `6780b79c`, the later units `f81d9b36`, `60b25b28`, `6c126713`, and
the nonadjacent-consumer exclusions listed below. Proof artifacts give 246
owning tasks. Among the 18 exclusions of this task, the only owner is
`8252833d`: its module `Classification.SegmentProductPermutation` (definition
artifact `0095a4c4`, also an auxiliary file of its proof artifact `b61f2ca8`) is
in the statement chain of `h35`/`hF`, and no declaration of it is used (below).
No linked-pair, swap, commutation or later-unit task owns a closure module.
The remaining owner hits are nonadjacent-consumer exclusions, treated in the
next subsection.

Definition artifacts record no owning task. Those published under excluded
tasks are the generic modules of the following table, as already audited in the
Markdown of `h35` and `hF`. Declaration counts are from the declaration audit
below.

| Module (under `Langlands.Representation`, except `Combinatorics`) | Artifact / publishing task | How reached | Declarations used |
| --- | --- | --- | --- |
| `Classification.TrivialGroupQuotient` | `1e56ed7e` / `20e4e1c6` | statement chain of `h35`/`hF` | 0 |
| `Classification.SegmentProductPermutation` | `0095a4c4` / `8252833d` | statement chain of `h35`/`hF` | 0 |
| `Classification.OrderedMultisegmentHeadReduction` | `6529dc85` / `ebea9a8a` | statement chain of `h35`/`hF` | 0 |
| `Classification.SegmentSocleProductData` | `29cea4fd` / `f3a69bc8` | statement chain of `h35`/`hF` | 0 |
| `Classification.SingletonSegmentSocle` | `8aac8ad9` / `f3a69bc8` | statement chain of `h35`/`hF` | 19: rank casts `castRank`, `castRankEquiv`, `isIrreducible_castRank`, `normalizedProductRankCastIso`, and `singletonSegmentInducedEquiv` (with their auxiliary proofs) |
| `Combinatorics.RelationInversions` | `9e971abc` / `f3a69bc8` | inside `h35` | 6: `relationInversions`, `relationPairCount` and equation lemmas |
| `Filtration.ObjectTransport` | `68054cb0` / `f3a69bc8` | inside the assembly, `hH`, `h35`, `hF` | 13: `ObjectRepFiltration.comp`, `compGradedEquiv`, `equivTransportGradedEquiv` |
| `Tensor.FiniteFiltration` | `1529e866` / `f3a69bc8` | inside the assembly, `hH`, `hF` | 4: `FiniteTensor.slotEquiv`, auxiliary proofs of `FiniteTensor.congrEquiv` |
| `Filtration.SingletonIso` | `3ee88231` / `8364e73f` | inside `hF` | 7: `RepFunctorFiltration.lengthOneGradedIso` |
| `Induction.EmptyProductUnit` | `273c225f` / `8364e73f` | inside `hF` | 14: empty-product evaluation and unit isomorphisms |
| `Classification.CuspidalProductDerivativeQuotientSupport` | `bf38b454` / `f81d9b36` | inside `h35`, `hF`, `hC` | 57: quotient form of BZ77 4.7(a) inside the BZ77 4.7(b) proof |
| `Classification.RegularLanglandsHeadReduction` | `1c0aecf1` (definition) | inside `h35` | 1: generic `RegularHeadExistence.nontrivial_normalizedProductInduction` |

The statement chain of `h35`/`hF` also reaches the statement module
`Classification.MultisegmentClassificationStatement` (`0baefc8e`). It names
`OrderedMultisegmentSocleExistence` and `SquareIntegrableLanglandsClassification`
only as proposition definitions; no declaration of it is used. The statement
modules `OrderedSegmentSquareIntegrableConversionStatement`,
`RegularLanglandsStatement` and `TemperedBlockStatement` are in the closure,
and none of their declarations is used either. The operator responses
`2b34e4035a5b5dafad7ad84d5a8c0dd8` and `10df3136f50c5901b1061d52c6b92e07`,
recorded in the Markdown of `h35` and `hF`, distinguish such generic
infrastructure from the excluded conclusions and allow the BZ77 4.7(b) closure.

### Detection and the nonadjacent-consumer restrictions

The task context carries the restrictions of the general detection unit and its
nonadjacent-product consumer (task `3c9849a4`), including the operator
conditions in correspondence `bd71b9185aab5d6eafffb7891bd3a3ca`. They bind
detection, its prerequisites and that consumer, and "do not prohibit the
separately specified Ze80 5.4/6.2 arguments in their respective consumers".
The objective of this task names Ze80 3.5 as an input of 6.3.

- The general detection unit is `Derivative.MirabolicDerivativeDetectionProof`
  (`mirabolicDerivativeDetection`, artifact `3ace613e`, task `ed056880`). It is
  used, through the assembly, `h35`, `hC`, `hD`, `hF` and `hH`. Its closure
  has 78 modules: no segment, socle or Jacquet-formula module, and no module
  owned by an excluded task. So the detection restrictions hold.
- The nonadjacent-product proof (`98cc1114`, task `3c9849a4`) has a closure of
  657 modules. Its only segment module is `Classification.Segments`; its only
  module owned by a nonadjacent-consumer exclusion is the generic
  `Classification.CuspidalIntegralTwistFreenessProof`.
- The modules of tasks named in the nonadjacent-consumer list enter this closure
  only through `h35` (Ze80 3.5) and `hF`, which imports `h35`:
  the proofs of `segmentSocleJacquetFormula` (`dbcb1209`, task `b95105c6`,
  with `SegmentSocleJacquetReduction`), `segmentFullJacquetFormula`
  (`f2c2886a`, task `b331611c`), `segmentZelevinskyConstituentExistence`
  (`7172c4a6`, task `4ca79bbd`), the two-supercuspidal structure
  (`f10f67f3` and `cc7183bf`, task `ab61f565`), the nonadjacent irreducibility
  (`98cc1114`, task `3c9849a4`, with `TwoSupercuspidalDerivativeBridge` and
  `NonadjacentAssembly`), and the task `67279e36` modules
  `CommonImageMultiplicityOneProof`, `CuspidalJacquetFunctorExactnessProof`,
  `MultiplicityOneConstituentProof`, `SegmentInductionAdmissibilityProof`,
  `SegmentJacquetMultiplicityProof`, `SegmentTensorReversalProof`,
  `SegmentTensorStabilizerProof`, `UpperJacquetSubrepresentationDetectionProof`,
  `CuspidalSupport.DistinctTensorStabilizerProof` and
  `Filtration.SimpleMapMultiplicityDetectionProof`. The Markdown of `h35`
  audits these inputs.
- One exception: `Classification.CuspidalIntegralTwistFreenessProof`
  (`a7545313`, task `67279e36`) is also used directly, by this task's
  `SegmentSocleProductCaseTwo`. Its theorem `cuspidalIntegralTwistFreeness`
  says only that `ρ ν^k ≅ ρ` forces `k = 0` for a supercuspidal `ρ`
  (central-character argument). It contains no special-head or reverse-socle
  existence result.
- No module of `ed48ae06`, `55ad1e10`, `92aea10f`, `aca8805b` or `5eece9e8` is
  in the closure.

### Declaration audit

A development check (`run_cmd` in a private draft importing this module, not
part of the candidate) collected every constant reachable from
`Langlands.Classification.segmentSocleProductHomogeneity` through
`getUsedConstantsAsSet`, transitively through the values and types of all
constants. Results (check `a0332091-51e8-4c91-8a56-bd0438b248ad`):

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
  `cuspidalIntegralTwistFreeness` (and the generic lemmas of the `67279e36`
  modules), all inside `h35` except the last, as stated above.

### Exclusion table

| Exclusion of this task (conclusion, proof successors, transitive dependencies) | Result |
| --- | --- |
| Ordered-socle existence `23189526` (`OrderedMultisegmentSocleExistence`) | No proof dependency; the name occurs only as a proposition definition in `MultisegmentClassificationStatement`, and no declaration of it is used. This task is a lower input of `23189526`; no module of the closure consumes the target. |
| Socle exhaustion `f3a69bc8` | Only the generic definition modules in the table above. |
| Analytic segment classification `aca8805b` | Absent. |
| Segment-socle product irreducibility `23e98d90` | Absent. |
| Final segment-socle irreducibility criterion `2ae5cbe5` | Absent. |
| `AdjacentUnlinkedSegmentSocleSwap` (tasks `e3634665`, `cded83f3`) | Absent. |
| `TwoSegmentSocleCommutation` (tasks `426911b4`, `66e3b87c`) | Absent. |
| Special-head product criterion `8364e73f` | Only the generic `SingletonIso` and `EmptyProductUnit` (inside `hF`). |
| Special-head exhaustion `3bfb61fa` | Absent. |
| Ordered special-head existence `ebea9a8a` | Only the definition module `OrderedMultisegmentHeadReduction` (statement chain of `h35`/`hF`, no declaration used). |
| Quotient coverage `20e4e1c6` | Only the definition module `TrivialGroupQuotient` (statement chain, no declaration used). |
| Tempered block uniqueness `52e97845` | Absent; the statement module `TemperedBlockStatement` is present with no declaration used. |
| `SquareIntegrableLanglandsClassification` / `1cb45da2` | Absent, except the proposition-definition name in `MultisegmentClassificationStatement`. |
| Square-integrable exhaustion `cd8ab97c` | Absent. |
| Regular exhaustion `bf433f0a` | Absent; from `RegularLanglandsHeadReduction` only the generic nontriviality lemma above. |
| `GenericSegmentProductUniqueness` / `30341ae4` | Absent. |
| Ordered special-segment conversion `8252833d` | Only the definition module `SegmentProductPermutation` (statement chain, no declaration used); the statement module `OrderedSegmentSquareIntegrableConversionStatement` is present with no declaration used. |
| Forward special-segment essential square-integrability `5eece9e8` | Absent. |
| Ze80 6.1(a) and later, linked-pair results, final product criteria, classification | Absent: no linked-pair, gluing, reverse-product or classification theorem is reachable. |

This audit checks mathematical dependencies. Publication of a generic module
under an excluded task is not treated as use of that task's conclusion, and a
statement definition or citation is not treated as a proof.

## Validation

The Lean source has SHA256
`84e9e12d67f1356a20d90bda6fc3188fc60ee91d534bd4be819eef919246a29c`.
`lean_check` in approved environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`
(check `73d56957-c9d5-4731-9c76-9ec2980fbdcc`, on the workspace at Library
commit `41034879`) built the module with zero errors and zero warnings. Inspection of
`Langlands.Classification.segmentSocleProductHomogeneity` reports universe
parameters `uF`, `uV` and only the axioms `propext`, `Classical.choice` and
`Quot.sound`. The file contains no `sorry`, `admit` or new axiom. Compilation
is not semantic acceptance; publication requires independent review and the
exact-target check.

No code was reused from drafts or from other workers; the module only applies
published theorems by name.
