# Cuspidal Jacquet modules of a product of two segment socles on one line, proof

Authors: Worker 1142 and Worker 1145 (the two executors of task
`343ddfde-e74c-46b8-a559-0c8f3a3145a6`). This module is the final assembly. It
copies no code: every input is a published declaration imported by Lean name.
Worker 1145 wrote the shuffle-filtration assembly `TwoSegmentShuffleAssembly`
and the plumbing of this module. Worker 1142 wrote the surviving-piece unit
`TwoSegmentShufflePieces` and this module's final form and Markdown. The proof
of Ze80 3.1 is the published `segmentFullJacquetFormula` of task
`b331611c-526d-4925-87fe-ea67ed6e6fed`.

## Statement proved

```lean
theorem Langlands.Classification.twoSegmentSocleShuffleJacquet
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    TwoSegmentSocleShuffleJacquet.{uF, uV, uW} F T
```

The theorem proves the published proposition
`Langlands.Classification.TwoSegmentSocleShuffleJacquet.{uF,uV,uW} F T` of
`Langlands.Representation.Classification.TwoSegmentSocleShuffleJacquetStatement`
(statement artifact `2081c976-7739-449f-a369-4f1aad69176f`, task
`efe00a4a-423f-449a-acf6-4e7e0eaf7f35`). The statement pair and every pair it
imports are unchanged. The outer telescope is exactly
`{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)`, and
the theorem has no further hypothesis and no theorem-valued premise. The
universes `uF`, `uV` and `uW` are independent level parameters; none is
saturated. `lean_check` inspection reports `level_parameters = [uF, uV, uW]`
and the axioms `propext`, `Classical.choice` and `Quot.sound` only.

The proposition says the following. Take a cuspidal datum `ρ` of rank `r` with
an actual supercuspidal representative `A`, reals `a₀, a₁`, naturals `m₀, m₁`
and a datum `d : T.SegmentProductDatum.{uV,uF} ((m₀ + m₁) * ρ.rank)` with
`d.length = 2` and `d.HasSegmentSocles`. Suppose segment `0` has beginning
`ρ.twist a₀` and length `m₀`, and segment `1` has beginning `ρ.twist a₁` and
length `m₁`. Let `C = BlockShape.uniform (m₀ + m₁) ρ.rank ρ.rank_pos` and
`J = CuspidalJacquetMultiplicity.upperJacquet T C d.induced.obj`. Then

1. `HasCompositionSeriesLength J ((m₀ + m₁).choose m₀)`, and
2. for every irreducible `τ` of `C.Levi F.Carrier` on a carrier in universe
   `uW` and every `m`, `HasJordanHolderMultiplicity J (Rep.of τ) m` holds iff
   `m` is the number of `S : Finset (Fin (m₀ + m₁))` with `S.card = m₀` whose
   shuffle tensor
   `FiniteTensor.externalSmoothObject (shuffleFactors F T A.obj (m₀ + m₁) ρ.rank_pos S a₀ a₁)`
   is equivalent to `τ`.

Since the theorem has exactly this type, it claims nothing beyond the
statement's Markdown.

## Implemented proof

The module contains two declarations.

```lean
theorem TwoSegmentShuffle.survivingPieceEquiv_of_segmentSubrepresentationFullJacquet
    (h31 : SegmentSubrepresentationFullJacquet.{uF, uV} F T) :
    SurvivingPieceEquiv.{uF, uV} F T :=
  fun _ A a₀ a₁ _ _ d h₂ hA hsoc hb₀ _ hb₁ _ h₀ h₁ w S R hS hR hdiv =>
    surviving_piece_equiv F T h31 A hA a₀ a₁ d h₂ hsoc hb₀ hb₁ h₀ h₁ w S R hS hR hdiv

theorem twoSegmentSocleShuffleJacquet ... :
    TwoSegmentSocleShuffleJacquet.{uF, uV, uW} F T :=
  TwoSegmentShuffle.twoSegmentSocleShuffleJacquet_of_survivingPieceEquiv F T
    (TwoSegmentShuffle.survivingPieceEquiv_of_segmentSubrepresentationFullJacquet F T
      (segmentFullJacquetFormula.{uF, uV} F T).1)
```

The first theorem is a bridge between the two supporting units. Its body only
reorders binders. `SurvivingPieceEquiv` (module `TwoSegmentShuffleAssembly`)
quantifies over the data of the target statement in its binder order. The
pointwise `surviving_piece_equiv` (module `TwoSegmentShufflePieces`) takes
explicit arguments and does not need the two length equations, which the
bridge discards. The second theorem feeds clause 1 of the published
`segmentFullJacquetFormula` (Ze80 3.1,
`SegmentSubrepresentationFullJacquet`) to the bridge and then to the
conditional assembly `twoSegmentSocleShuffleJacquet_of_survivingPieceEquiv`.
`segmentFullJacquetFormula` is used at universes `uF, uV`, the universes of
`SurvivingPieceEquiv`. The assembly theorem is universe-polymorphic in `uW`.

The mathematical route, implemented in the two supporting units, follows
Zelevinsky 1980, 1.6 and 3.1. Write `r = ρ.rank`, `B = d.shape` for the
two-block shape `(m₀ r, m₁ r)`, and `σ₀, σ₁` for the socles `d.blocks`.

1. *Geometric lemma* (`TwoSegmentShuffleAssembly.shuffleJacquet_of_pieces`).
   The published `Geometric.padicGeometricLemma`, at carrier universe
   `max uF uV`, filters `J = r_C(i_B(σ₀ ⊗ σ₁))` by the minimal double-coset
   representatives `w` for `(B, C)`. The graded piece of `w` is the geometric
   piece `(geometricPieceFunctor T B C w S R hS hR).obj (σ₀ ⊗ σ₁)`.
2. *Vanishing* (`geometricPiece_subsingleton_of_not_dvd`). If some piece of
   the source refinement `S` has size not divisible by `r`, the normalized
   Jacquet module of the corresponding socle along that refinement is zero
   (`IsSegmentSocle.jacquet_subsingleton_of_not_dvd`, the vanishing in the proof
   of Ze80 3.4). So the whole geometric piece is zero
   (`SegmentEdge.refinedJacquet_external_subsingleton`,
   `SegmentEdge.geometricPiece_subsingleton`).
3. *Surviving pieces* (`TwoSegmentShufflePieces.surviving_piece_equiv`).
   If every piece of `S` has size divisible by `r`, the conjugated
   intersection Levi is the Levi of `C`
   (`ShuffleRefinement.conjugatesLevi_flatten_uniform`). Then the piece is the
   transport along `w` of the refined Jacquet module of `σ₀ ⊗ σ₁`
   (`Geometric.wholeLeviGeometricPieceEquiv`). That module is the tensor of the
   Jacquet modules of `σ₀` and `σ₁` (`RefinedJacquetTensor.jacquetEquiv`). By
   Ze80 3.1 (`h31`; `IsSegmentSocle` implies `IsSegmentSubrepresentation`) the
   Jacquet module of `σⱼ` along its uniform refinement is
   `⊗ᵢ ν^i A'` (`segmentFactors A'`, factors `A', νA', …`) for a
   representative `A'` of the segment base `ρ.twist aⱼ`. Then
   `JuxtaposedShuffle.nonempty_cast_iso` identifies each `ν^i A'` with
   `ν^(aⱼ+i) A`, so this Jacquet module is `⊗ᵢ ν^(aⱼ+i) A`.
   The transport `CuspidalSupport.transportEquiv` and
   `ShuffleRefinement.uniformRefinementTensorEquiv` reorder the nested tensor
   into the shuffle tensor of the subset
   `S' = ShuffleRefinement.refinementShuffle … w S …`. The exponents agree by
   `shuffleExponent_refinementTargetIndex_zero` and `_one`.
4. *Deletion and indexing.* `ObjectRepFiltration.zeroFactorDeletionTheorem`
   deletes the zero pieces. `ShuffleRefinement.divisibleEquivShuffles`
   identifies the surviving representatives with
   `{S : Finset (Fin (m₀ + m₁)) // S.card = m₀}`, compatibly with
   `refinementShuffle`.
5. *Counting.* Each shuffle tensor is irreducible
   (`shuffleTensor_isIrreducible`, from `CuspidalSupport.glCuspidalTensor`).
   `finiteFamilyFiltrationMultiplicity` gives a composition series of length
   `Nat.card {S // S.card = m₀} = (m₀ + m₁).choose m₀`
   (`Fintype.card_finset_len`). It also gives the Jordan–Hölder multiplicity of
   every `τ` in universe `uW` as the number of shuffles whose tensor is
   equivalent to `τ`.

The Markdown files of `TwoSegmentShuffleAssembly` and `TwoSegmentShufflePieces`
describe each step with its hypotheses.

## Scope

The theorem keeps arbitrary primes, finite p-adic fields, the supplied
compatible topology `T`, arbitrary real `a₀, a₁` and natural `m₀, m₁`, and
repeated, equal and linked segments. It uses the actual upper normalized
product induction `d.induced` and the actual upper normalized Jacquet module
`upperJacquet`. It adds no finite-length, irreducibility, genericity, linkage or
distinctness premise. The socles have carriers in `max uF uV`, and the geometric
lemma is used at that universe. `τ` ranges over carriers in the independent
universe `uW`.

## Sources

- A. V. Zelevinsky, *Induced representations of reductive p-adic groups II.
  On irreducible representations of GL(n)*, Ann. Sci. ENS (4) 13 (1980): §1.6
  (printed pp. 171–172), the coordinate form of the geometric lemma; §3.1
  (printed pp. 180–181), the Jacquet module of `⟨Δ⟩`; the proof of
  Proposition 3.4 (printed p. 181), the vanishing along compositions that are
  not made of multiples of `r`. Literature ID `zelevinsky-1980-induced-ii`,
  SHA-256 `663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
- I. N. Bernstein and A. V. Zelevinsky, *Induced representations of reductive
  p-adic groups I*, Ann. Sci. ENS (4) 10 (1977), 2.12, the geometric lemma
  (printed p. 448). Literature ID `bernstein-zelevinsky-1977-induced-i`.

The Lean route follows the four steps of these sources. The piece
identification goes through the whole-Levi transport and the refined Jacquet
tensor equivalence of the Library rather than Zelevinsky's matrix notation.

## Dependency audit

All counts and checks below refer to Library commit
`fcac121256163a8da6dd01a9483e1104a9b92aba`. Module names in tables omit the
prefix `Langlands.`.

### Direct inputs

| Input (module) | Artifact, task | Use |
| --- | --- | --- |
| `segmentFullJacquetFormula` (`Representation.Classification.SegmentFullJacquetProof`) | proof `f2c2886a-997f-43e7-8c4d-59649a68b475`, task `b331611c-526d-4925-87fe-ea67ed6e6fed` (Workers 890 and 964) | Clause 1 is Ze80 3.1, `SegmentSubrepresentationFullJacquet`. This is the input named by the task. It is not duplicated. |
| `TwoSegmentShuffle.SurvivingPieceEquiv`, `twoSegmentSocleShuffleJacquet_of_survivingPieceEquiv` (`Representation.Classification.TwoSegmentShuffleAssembly`) | supporting unit `d2276d74-efd1-48d4-9060-bb0c3a063221`, this task, Worker 1145 | Geometric-lemma filtration, vanishing, deletion, indexing and counting, conditional on `SurvivingPieceEquiv`. |
| `TwoSegmentShuffle.surviving_piece_equiv` (`Representation.Classification.TwoSegmentShufflePieces`) | supporting unit `c3b5dddf-8bad-47ca-a7de-5e9ef379e7d1`, this task, Worker 1142 | Surviving pieces, conditional on Ze80 3.1. |

The geometric lemma `Geometric.padicGeometricLemma`
(`Representation.Geometric.GeometricLemmaProof`, proof
`f606bb75-3194-405e-ba6a-1edb4294d539`, task
`67ebcf61-3d58-4499-9c0c-c847e90aaeb4`) is the other input named by the task.
`TwoSegmentShuffleAssembly` uses it, and it is not duplicated. The two
supporting units list their own direct inputs, with tasks, in their Markdown.

### Import closure

A recursive scan of the `import` lines gives 1055 project modules in the
transitive closure, this module included. The closure of each direct import:

- `SegmentFullJacquetProof`: 1038 modules. It contains the closure of Ze80 1.11,
  `TwoSupercuspidalProductStructureProof` (proof
  `f10f67f3-8c77-43b5-8eef-0e25e3e9b964`, task
  `ab61f565-1427-4746-ba77-46097563e962`), with 879 modules.
- `TwoSegmentShuffleAssembly`: 373 modules.
- `TwoSegmentShufflePieces`: 183 modules.

Their union is the whole closure except this module. Of the 1054 imported
modules, the Library registry records 247 as the entry module of a published
proof, 336 as the entry module of a published definition or supporting unit and
218 as that of a published statement. The remaining 253 modules are helper
modules shipped with these artifacts, or modules from the project's first
proof rounds, which have no current registry record.

### Exclusions

The checks below cover the exclusions of this task. These are the tasks
`a55c4267`, `0c90f7e4`, `8fa9f68b`, `2ae5cbe5`, `e3634665`, `cded83f3`,
`426911b4`, `66e3b87c`, `c84cd52c`, `6780b79c`, `23189526`, `f3a69bc8`,
`aca8805b`, `3bfb61fa`, `ebea9a8a`, `20e4e1c6`, `52e97845`, `1cb45da2`,
`cd8ab97c`, `bf433f0a` and `8364e73f`. They also cover
`LinkedSegmentSocleReverseProductQuotientHom`: statement task
`7ff2a1e9-89dc-439e-a861-a567b3db92bf` and proof successor
`ba6ec030-6fd9-4f87-84f1-0e1e82ae46da`.

- *Registry records.* For every module of the closure, every published registry
  record of which it is the entry module was compared with these 23 task IDs.
  None of the records is a statement or proof of an excluded task. The only
  matches are eleven definition-kind supporting units, explained below.
- *Declaration names.* No Lean file of the closure contains any of the names
  `LinkedSegmentSocleReverseProductStructure`,
  `JuxtaposedSegmentSocleReverseProductStructure`,
  `LinkedSegmentSocleReverseProductQuotientHom`,
  `LinkedSegmentSocleReverseProductSteps`, `LinkedSegmentSoclePairReducible`,
  `SegmentSocleProductIrreducibility`, `UnlinkedSegmentSocleProductIrreducible`,
  `AdjacentUnlinkedSegmentSocleSwap`, `TwoSegmentSocleCommutation`,
  `TwoFactorProductConstituentCommutativity`, `LinkedSegmentSocleGluing`,
  `OrderedMultisegmentSocleExistence`, `MultisegmentSocleExhaustion`,
  `SegmentEssentialSquareIntegrableClassification`,
  `MultisegmentHeadExhaustion`, `OrderedMultisegmentHeadExistence`,
  `OrderedMultisegmentQuotientExhaustion`, `TemperedBlockUniqueness`,
  `SquareIntegrableLanglandsClassification`,
  `SquareIntegrableLanglandsExhaustion`, `GLRegularLanglandsExhaustion`
  or `SegmentHeadProductIrreducibility`. These are the targets of the
  excluded tasks.
- *Task identifiers in files.* No Lean file of the closure contains any of
  the 23 task-ID prefixes. They occur only in Markdown files. There they appear
  in independence lists that record those tasks as absent, for instance
  `Derivative.OrderRecursion`, `Filtration.Splicing`,
  `Parabolic.RefinedJacquetTensor` and `SegmentFullJacquetProof`. They also
  appear in the filing notes of the supporting units below.

Supporting units filed under excluded tasks. Nine finite supporting units of
Worker 167 were published under task `0c90f7e4-78fa-43fd-8736-238bb3e8617d`
(`JuxtaposedSegmentSocleReverseProductStructure`):

| Module | Supporting unit |
| --- | --- |
| `Representation.Classification.JuxtaposedRefinementTools` | `49643601-1f9c-4c1b-bac6-2a2269138d08` |
| `Representation.Classification.TwoSourceShuffleLabels` | `6324c466-f187-49e5-ba73-cbf7b5a12a89` |
| `Representation.Classification.UniformJacquetVanishing` | `7474c907-7494-4934-927c-a643fa565c6e` |
| `Representation.Classification.UniformRefinementCombinatorics` | `18231764-fb7e-402c-9890-bd825da3af72` |
| `Representation.Classification.UniformRefinementCoordinates` | `a5dd707e-d6ca-482f-b2f4-6c1dface8877` |
| `Representation.Classification.UniformRefinementLeviTransport` | `de9b4338-186c-4728-b213-eee99db24d17` |
| `Representation.Classification.UniformRefinementShuffleRealization` | `ceacade2-81f9-43a6-b367-e690e79a271d` |
| `Representation.Classification.UniformRefinementSurvivors` | `e4622c15-8740-414c-aa94-7f4be9a0e3b5` |
| `Representation.Classification.UniformTargetBlockLabels` | `c4f50f7f-3046-449f-9528-8a51ad911304` |

They contain finite coordinates, shuffle labels, Levi and tensor transport,
twist transport and the vanishing of Jacquet modules of segment socles along
shapes with a part not divisible by the cuspidal rank. They are upstream
inputs of that structure theorem, not its exact proof or one of its
conclusions. Their closures lie inside the closure audited here, so they
contain no statement, proof or name of an excluded result. They assume neither
the target of task 0c90f7e4 nor any other excluded result. The accepted audits of
`TwoSegmentShuffleAssembly` and `TwoSegmentShufflePieces` record the same
finding. Since none of them imports this module, there is no circularity.

Two lower units were published under the socle-exhaustion task
`f3a69bc8-7312-4f82-8a7d-ea3c8188cb63`:

- `Representation.Filtration.ObjectTransport` (definition `68054cb0-7541-498d-bd52-0414519d5815`).
  It pulls an `ObjectRepFiltration` back along a monoid homomorphism and
  transports it along an equivalence. Its only import is
  `Filtration.LengthTwoMatching`. The supporting units reach it through
  `Tensor.ProductFiltration`, which `SegmentEdgeJacquetReduction` imports. The
  1.11 and 3.1 closures also reach it through `NonadjacentSpecialization` and
  `OppositeCuspidalJacquetFiltrationProof`.
- `Combinatorics.RelationInversions` (definition `9e971abc-0144-4575-8205-89a2ae397e63`,
  Worker 494). It counts inversions of a decidable relation on finite lists, and
  it imports only Mathlib. It is reached only inside the 1.11 closure, through
  `Group.GL.UpperBruhatFiltration`.

Both are generic infrastructure that asserts no representation-theoretic
theorem. Neither is a conclusion or proof of `MultisegmentSocleExhaustion`, and
neither imports anything from task `f3a69bc8`.

### Derivative results

This module and its two supporting units state, construct and prove nothing
about derivatives. Neither supporting-unit closure contains a module named
`Derivative`, `Mirabolic` or `GelfandKazhdan`. Their only module named
`Whittaker` is `Whittaker.Iwasawa`, the Iwasawa decomposition of `GL_n`.

The task names the published proof of `SegmentFullJacquetFormula` as an input.
That proof uses Ze80 1.11 (`twoSupercuspidalProductStructure`, task
`ab61f565`), which proves BZ77 Theorem 4.2 with the Bernstein–Zelevinsky
derivative theory. So the 1.11 closure contains 158 modules named
`Derivative`, `Mirabolic`, `Whittaker` or `GelfandKazhdan`, and all of them lie
inside it. They include the derivative functors and their exactness (tasks
`d3e94f0f`, `44f58b77`), the BZ77 4.13–4.14 product and Leibniz filtrations
(`6cd54f76`, `7e19f753`, `3231134e`, `4e10058b`), and the supercuspidal
derivative vanishing and one-dimensional top derivative of BZ77 4.4
(`2e5183b1`, proof `fd42c8ef`). They also include Whittaker multiplicity one
(`209cde88`) and the Gelfand–Kazhdan realization (`2206daa6`). Every one of
these is published and independently accepted, and none is a hypothesis of
any step. They enter this proof only through the task-mandated input
`SegmentFullJacquetProof`. The present task neither duplicates them nor uses
them directly.

The closure contains no segment derivative formula. A text search for
`SegmentSocleDerivatives`, `HighestDerivativeSupportShift`,
`NonjuxtaposedSegmentSocleConstituentLevel`, `SegmentHeadJacquetFormula` and
`SegmentSocleJacquetFormula` over its Lean files finds nothing. No registry
record of the closure belongs to tasks `209027ca` (Ze80 3.5), `60b25b28`
(Ze80 4.3), `f81d9b36` (BZ77 4.7(b)), `4e152d19` (highest derivative of
segment-socle products) or `8e5b4563`. The Markdown of
`SegmentFullJacquetProof`, section "Derivative results", records the
corresponding audit of the 1.11 route. It also records the trusted operator's
decision on request `a8463ee15d57588c8de10306748b2538` (correspondence
`bd71b9185aab5d6eafffb7891bd3a3ca`). That decision allows a fully proved BZ77
derivative route, without Ze80 3.5 or 9.6 and without excluded tasks.

### Proved-module inventory

The first table lists every closure module that the Library registry records
as the entry module of a published proof (247 modules), with its proof
artifact and the task it was proved under. None of these tasks is excluded.

| Proved module | Proof artifact | Task |
| --- | --- | --- |
| `Algebra.SandwichDimensionBoundProof` | `a4c517c5` | `21b68369-cc3e-42af-8d47-03a5bb4d8d34` |
| `Analysis.Local.CompactOpenCoverUnimodularityProof` | `a9cc9564` | `071e4d23-2827-49e3-953a-b755c243d302` |
| `Analysis.Local.QuotientAutomorphismProof` | `9eef24ba` | `88e8f6c0-c9cf-40fb-90e5-2ddbb72cc479` |
| `Analysis.Local.QuotientAveragingKernel` | `e260634d` | `4ecaafca-57e4-472e-9501-7cf362d21007` |
| `Analysis.Local.QuotientMeasureExistence` | `675cd3b8` | `7d14a606-bb49-4cf0-9f89-8034e21e9f15` |
| `Analysis.Local.QuotientPositiveLifting` | `e8eb5c9d` | `40466063-2de2-456b-ae79-93c782b76e0b` |
| `Galois.Local.AbsoluteProof` | `f92d202b` | `784bfe1b-4a1c-4925-8b83-5e2fbbb2de91` |
| `Group.GL.BlockContractionProof` | `92813962` | `7cb3dbc0-fae7-4e88-a79f-d0dcc19aaee5` |
| `Group.GL.BlockIwahoriBasis` | `c110ea11` | `9c364114-a50b-4402-ac9b-63b12dfb9484` |
| `Group.GL.BlockModulusHaarProof` | `3008bd3f` | `d9c54335-005e-4ebb-afed-7c05912388a8` |
| `Group.GL.BlockUnipotentHaarProof` | `69cecf67` | `d9c54335-005e-4ebb-afed-7c05912388a8` |
| `Group.GL.CartanProof` | `fd42961a` | `506fa0e8-79ea-41fb-85da-18cc6dadceab` |
| `Group.GL.CentralQuotientTopologyProof` | `7fe122eb` | `6ee0f696-9c8a-40ab-b8d0-210ae1ecd734` |
| `Group.GL.CountabilityProof` | `dd877404` | `67ebcf61-3d58-4499-9c0c-c847e90aaeb4` |
| `Group.GL.InverseTransposeIwahoriProof` | `ee599ebf` | `05abc80d-aec1-4f31-92fc-846b13a15ec2` |
| `Group.GL.MirabolicMixedOrbitCoverageProof` | `2178f392` | `b7304e81-6082-4291-834f-fff6f448590b` |
| `Group.GL.MirabolicModularCharacterProof` | `bfba0d9f` | `518f986d-21ce-44ac-bd2e-80e6b1e15561` |
| `Group.GL.MirabolicModulusProof` | `f25fdd6c` | `f947a735-872d-44db-a9ea-954d17dec4bd` |
| `Group.GL.PrincipalBlockFactorizationProof` | `c4f3e890` | `069d1e18-b908-42cb-b064-af1237ba4e7c` |
| `Group.GL.UpperBruhatBoundaryProof` | `1200687b` | `2fe252f9-125b-47cf-9277-20271ef24b1b` |
| `Group.GL.UpperBruhatCoordinatesProof` | `3dbfe83b` | `fd59b42f-6374-40fa-91ea-0dd9de25ea17` |
| `Group.GL.UpperBruhatFiltrationGeometryProof` | `0bfabde5` | `804989b0-fc9d-4e19-b339-ddddb5f0e143` |
| `Group.GL.UpperBruhatLocalClosednessProof` | `c95cbd74` | `080c7802-956c-4b53-8077-3535aebc8f2b` |
| `Group.GL.UpperBruhatPivotProof` | `3cb9fdc0` | `cb1e92a3-bf5e-4765-a993-c41522dd0022` |
| `Group.GL.UpperBruhatProof` | `870ed2b8` | `8c2f6593-d22c-44b1-be0b-4ad6cb08445f` |
| `Group.GL.UpperBruhatRankProof` | `bf240f56` | `5ded0ee0-107f-4026-8f4d-2914271951e0` |
| `Group.GL.UpperBruhatTransposeProof` | `fb12f422` | `a0748df8-d292-4712-b136-5d497f20c6e7` |
| `Group.GL.UpperUnipotentCompactContainmentProof` | `5245f863` | `4d4af694-8d02-4337-86cb-260fe32fdbea` |
| `Group.GL.UpperUnipotentFactorizationProof` | `bca2c4cb` | `a8e4c0ca-ae06-4409-a11f-83ea76aefd10` |
| `HarmonicAnalysis.Distribution.BruhatFiltrationVanishingProof` | `f19bf4cc` | `bfcbbf63-ceae-4164-a704-2df59ca54f67` |
| `HarmonicAnalysis.Distribution.CharacterAverageCovarianceProof` | `c6cadd36` | `71db8a18-f07f-4ab5-903a-dad529415e84` |
| `HarmonicAnalysis.Distribution.CharacterAverageFactorizationProof` | `a8683405` | `0b4011fc-a687-4bd8-b8b3-d1516f7cc6cd` |
| `HarmonicAnalysis.Distribution.CharacterAverageSurjectiveProof` | `f5ed0e18` | `7ce05a8f-e5f8-4e6b-a8d4-d09cba4a5b8e` |
| `HarmonicAnalysis.Distribution.ClosedRestrictionProof` | `9f1d0056` | `e30739f3-023e-4ab9-8420-03f4b6371108` |
| `HarmonicAnalysis.Distribution.ClosedSupportedDescentProof` | `9f406413` | `3c0bd25b-3ebd-49a0-800a-966e900dbb39` |
| `HarmonicAnalysis.Distribution.FiniteOrbitVanishingProof` | `2cc18a52` | `51a122ec-9363-4c38-9df9-593ffdb99219` |
| `HarmonicAnalysis.Distribution.HomogeneousPositivityProof` | `ec24ad2f` | `af88fd57-87dd-4c4a-8a43-76f66553d80f` |
| `HarmonicAnalysis.Distribution.HomogeneousVanishingProof` | `0dcd54e0` | `4135f71e-a810-48af-8bd6-a199c17327da` |
| `HarmonicAnalysis.Distribution.LocalizationProof` | `8f3e3767` | `0c56480a-d0f8-4156-be1b-c331baa7dadd` |
| `HarmonicAnalysis.Distribution.OpenRestrictionLocalityProof` | `46428fca` | `b559bab6-0abe-483a-b982-d9b9c83187f0` |
| `HarmonicAnalysis.Distribution.SupportedDescentCovarianceProof` | `a18c6361` | `63fd1dbc-b930-474b-bfb0-6728e917a2e2` |
| `HarmonicAnalysis.Distribution.TransposeInvariantProof` | `a273f153` | `f9ba6d55-99f2-4ae7-93ad-0878f9bc7eb9` |
| `HarmonicAnalysis.PadicAdditiveConductorProof` | `8f35e474` | `e74b11cc-3905-4817-b499-dd50ea4f55f0` |
| `HarmonicAnalysis.PadicRectangularHaarScalingProof` | `4d3a028e` | `0e28951e-9779-4567-b8b0-c95334854fac` |
| `HarmonicAnalysis.PadicScalarHaarScalingProof` | `391187ae` | `574c1368-49a7-48eb-a084-18006b0f2871` |
| `HarmonicAnalysis.PadicUnitaryAdditiveCharacterExistsProof` | `72e1678f` | `2dbce78d-1f86-48f6-94e1-f32abb3be555` |
| `HarmonicAnalysis.RowTensorDecompositionProof` | `5d850fc9` | `3d0044b1-369c-4dc6-9f09-db47aec3ad6d` |
| `HarmonicAnalysis.RowTestSmoothProof` | `903c63ec` | `5998b0b2-e367-4e85-8d4d-47e3b9b4a222` |
| `HarmonicAnalysis.TriangularTranslationProof` | `59aa9379` | `7f443547-d49c-4edd-ba7e-9f0fb9d6ad67` |
| `LinearAlgebra.CyclicQuotientPairingProof` | `b1614c57` | `04ac0d48-00f1-428b-9d7e-afdfee7e4512` |
| `LinearAlgebra.MatrixAEvalConjugacyProof` | `5177f474` | `e82ee8d6-204c-40ac-85b0-968fb0a6a298` |
| `LinearAlgebra.MatrixCharpolyConjugacyProof` | `bbdcaa84` | `e82ee8d6-204c-40ac-85b0-968fb0a6a298` |
| `LinearAlgebra.MatrixTransposeConjugateProof` | `ffe32e49` | `a6652e7a-61f5-408f-a2b2-bfe81c3a2361` |
| `LinearAlgebra.PolynomialModuleBoundedCyclicDecompositionProof` | `da74a1b6` | `6ec62b7e-e127-438d-9e71-f96ea2435fab` |
| `LocalField.SmoothCharacterNormProof` | `92aab2ff` | `fc38422f-e429-4f03-8033-8e5dbbb6c12c` |
| `Representation.Character.SeparationProof` | `a68eef2b` | `50357f3e-0d26-4004-8ca0-562b7c8c3045` |
| `Representation.Character.TransportProof` | `83f963a8` | `25af224a-861b-48d6-9a6f-76284babdde5` |
| `Representation.Classification.ConstituentCompatibilityAlgebraicProof` | `c58d850a` | `bf9c99f4-41e2-41f2-a3df-970ab1e0a022` |
| `Representation.Classification.CuspidalIntegralTwistFreenessProof` | `a7545313` | `67279e36-f3c2-42e3-9302-11729784042e` |
| `Representation.Classification.IrreducibleProductEmbedding` | `18400cbf` | `974d403b-305c-4c06-8dff-d4efb438993f` |
| `Representation.Classification.IrreducibleTwoFactorProductSwapProof` | `be6157e1` | `0988a3e0-a086-474d-b2d2-7e53902b43cb` |
| `Representation.Classification.OppositeCuspidalJacquetFiltrationProof` | `75b961f6` | `efffd9ec-2492-4b9e-9425-e52e9146406b` |
| `Representation.Classification.SegmentConstituentCentralCharacterProof` | `fb068e0c` | `5093df28-71e8-4409-8477-a2880e392688` |
| `Representation.Classification.SegmentFullJacquetProof` | `f2c2886a` | `b331611c-526d-4925-87fe-ea67ed6e6fed` |
| `Representation.Classification.SegmentInductionAdmissibilityProof` | `b44b1180` | `67279e36-f3c2-42e3-9302-11729784042e` |
| `Representation.Classification.SegmentTensorStabilizerProof` | `1e385864` | `67279e36-f3c2-42e3-9302-11729784042e` |
| `Representation.Classification.SupercuspidalContragredientProof` | `a090c713` | `1c921aca-ebef-4c0c-8c38-63156b8e2930` |
| `Representation.Classification.SupercuspidalDerivativesProof` | `fd42c8ef` | `2e5183b1-01e9-44fb-b26c-f4521a25c7c7` |
| `Representation.Classification.TwistedProductCharacterTwistProof` | `ed7a2cff` | `c9fc6804-0810-4bdd-afd6-703678856df8` |
| `Representation.Classification.TwoBlockExponentNonUnitarizabilityProof` | `ee4360e4` | `a0b83fd9-00fd-4ce7-8aa6-35348b04e19f` |
| `Representation.Classification.TwoSupercuspidalAdjacentReducibilityProof` | `5d030a71` | `0988a3e0-a086-474d-b2d2-7e53902b43cb` |
| `Representation.Classification.TwoSupercuspidalNonadjacentIrreducibilityProof` | `98cc1114` | `3c9849a4-a6c0-43ac-9982-d15ed76bf1e9` |
| `Representation.Classification.TwoSupercuspidalProductStructureProof` | `f10f67f3` | `ab61f565-1427-4746-ba77-46097563e962` |
| `Representation.CompactCoefficient.SemisimplicityProof` | `1e1f8f18` | `d5a1f78e-156e-40a1-bf22-b80779eda1ce` |
| `Representation.Conductor.PrincipalCongruenceBasisProof` | `1a11e01c` | `ec709f88-fe65-43ae-8db1-13e4baf10217` |
| `Representation.CuspidalSupport.AssociatedGeometricPieceVanishingProof` | `3d3f251a` | `2bef39b2-3425-40f0-87e2-9a9b776e2ac7` |
| `Representation.CuspidalSupport.AssociatedGeometricPiecesEquivalenceProof` | `d5bbef23` | `17247e03-9471-4f13-81fa-e4f7058619a0` |
| `Representation.CuspidalSupport.AssociatedGeometricPiecesProof` | `5e121583` | `2bef39b2-3425-40f0-87e2-9a9b776e2ac7` |
| `Representation.CuspidalSupport.AssociatedProof` | `df6d40a0` | `6fe38fdd-fc45-4d32-9221-5b7788ee51f2` |
| `Representation.CuspidalSupport.AssociationLawsProof` | `a3d0cdf6` | `944b9b06-1e87-42d1-a565-00395593eb8b` |
| `Representation.CuspidalSupport.CompactCoefficientFinitenessProof` | `a23cbcdb` | `6884361c-0ab2-41b3-8098-9c070c4a1b3e` |
| `Representation.CuspidalSupport.CuspidalEmbeddingProof` | `b518020e` | `d1684637-cf80-4266-8850-2d68c922d008` |
| `Representation.CuspidalSupport.CuspidalTensorAssociationProof` | `e209fa9f` | `ee36e054-716f-492a-a0e3-e83b614d9431` |
| `Representation.CuspidalSupport.CuspidalTensorProof` | `8513f998` | `cece816e-aee9-40ca-9139-d770491b6178` |
| `Representation.CuspidalSupport.CuspidalityComparisonProof` | `b38138d8` | `e2c46108-7f86-4c0b-994d-3f34704b0261` |
| `Representation.CuspidalSupport.DeterminantUnitCentralCompactnessProof` | `6a6fd8f2` | `dc05b10a-c1b1-467d-a904-a871f9d6c6e9` |
| `Representation.CuspidalSupport.DeterminantUnitStructureProof` | `cc102593` | `bb7d9bb8-8b90-41e5-8005-9d81271939af` |
| `Representation.CuspidalSupport.DistinctTensorStabilizerProof` | `7c0d8ba0` | `67279e36-f3c2-42e3-9302-11729784042e` |
| `Representation.CuspidalSupport.FiltrationQuasicuspidality` | `79dd0677` | `6fe38fdd-fc45-4d32-9221-5b7788ee51f2` |
| `Representation.CuspidalSupport.HarishChandraAssembly` | `ccad91d6` | `e28d3ffc-81b2-49c6-a66a-9a344a79e95a` |
| `Representation.CuspidalSupport.HarishChandraBoundaryProof` | `b63b3325` | `e28d3ffc-81b2-49c6-a66a-9a344a79e95a` |
| `Representation.CuspidalSupport.HarishChandraConverseProof` | `c9152dba` | `b7830d5b-ebb6-42e5-85f3-5b8f39a312d2` |
| `Representation.CuspidalSupport.JacquetSubquotientProof` | `a3d3a114` | `b605839f-d645-4427-892a-04dd871b7c49` |
| `Representation.CuspidalSupport.LeviAdmissibleFactorizationProof` | `908ea769` | `3201c31a-f357-4b17-abc2-e22fb1a8938a` |
| `Representation.CuspidalSupport.LeviQuasicuspidalDecompositionProof` | `c0976267` | `2aacacad-31d0-47b4-9701-ac3865c0efbe` |
| `Representation.CuspidalSupport.LeviTensorFactorizationProof` | `cf3ee414` | `334e2222-c3e9-47e3-b05c-2afe12f49e94` |
| `Representation.CuspidalSupport.LeviTensorReflectionProof` | `60fde00b` | `0bd67a39-f7bb-49cd-a608-2521b22c6c42` |
| `Representation.CuspidalSupport.MinimalConjugatingCosetsProof` | `ea18e1f7` | `d042dc77-fd25-4c92-b943-d456ffd86fe9` |
| `Representation.CuspidalSupport.MinimalJacquetProof` | `dd0f42fe` | `f28607f5-1eef-4329-ae18-2576ef25ab6a` |
| `Representation.CuspidalSupport.MinimalWeylTransportProof` | `6acd6deb` | `2bef39b2-3425-40f0-87e2-9a9b776e2ac7` |
| `Representation.CuspidalSupport.NonassociatedJacquetSubquotientsProof` | `8c6610e7` | `b17b8c8c-858b-4b48-994b-e3641cb05f02` |
| `Representation.CuspidalSupport.ProperInductionProof` | `325eaa76` | `7b91ddfb-d311-47d0-9994-a5256dcdd85d` |
| `Representation.CuspidalSupport.QuasicuspidalEmbeddingProof` | `78f65422` | `efbb43fc-b6ce-4376-8e50-96b28dd6f5a6` |
| `Representation.CuspidalSupport.QuasicuspidalJacquetVanishingProof` | `134889be` | `b17b8c8c-858b-4b48-994b-e3641cb05f02` |
| `Representation.CuspidalSupport.QuasicuspidalLeviAdmissibilityProof` | `c862f739` | `e1237fc1-de75-4a4d-924b-d509dc475361` |
| `Representation.CuspidalSupport.StandardJacquetComparisonProof` | `8101b5b6` | `e2c46108-7f86-4c0b-994d-3f34704b0261` |
| `Representation.CuspidalSupport.TotalConjugatingCountProof` | `85ce2829` | `5becc159-1242-4fa4-9102-79aa6e2726c0` |
| `Representation.CuspidalSupport.ZeroRankEmbeddingProof` | `4211499e` | `d1684637-cf80-4266-8850-2d68c922d008` |
| `Representation.Derivative.GeneralLinearDerivativeExactnessProof` | `79bbad40` | `44f58b77-789a-478c-ba92-9e33b00c8a23` |
| `Representation.Derivative.GeneralLinearDerivativeLeibnizFiltrationProof` | `c4c5439d` | `4e10058b-cc0b-4ad5-ae78-365562f533e7` |
| `Representation.Derivative.LeftMixedProductDerivativeProof` | `e99bbe1b` | `7e19f753-4515-4d87-9256-f366b6fc5683` |
| `Representation.Derivative.MirabolicDerivativeDetectionProof` | `3ace613e` | `ed056880-a4dc-4ebf-ad26-9878e508cf6c` |
| `Representation.Derivative.MirabolicHighestDerivativePairingProof` | `f957ae76` | `a925b519-9bb9-4927-873e-ad322d41328e` |
| `Representation.Derivative.MirabolicMinusExactnessProof` | `d307cd07` | `b65bc667-6951-4bd5-82af-10fb7046df7f` |
| `Representation.Derivative.MirabolicMinusPairingTransferProof` | `5715a6a0` | `96a1c747-9282-43a2-b8b7-d9180675f432` |
| `Representation.Derivative.MirabolicProductMinusBoundary` | `c8340e2a` | `6cd54f76-f453-4faa-818a-5843e1bbcaff` |
| `Representation.Derivative.MirabolicProductMinusLeftPhi` | `e32e2414` | `6cd54f76-f453-4faa-818a-5843e1bbcaff` |
| `Representation.Derivative.MirabolicProductMinusLeftPsi` | `8a6a0658` | `6cd54f76-f453-4faa-818a-5843e1bbcaff` |
| `Representation.Derivative.MirabolicProductMinusRightBoundary` | `58a3c341` | `6cd54f76-f453-4faa-818a-5843e1bbcaff` |
| `Representation.Derivative.MirabolicProductMinusRightPhi` | `5449db58` | `6cd54f76-f453-4faa-818a-5843e1bbcaff` |
| `Representation.Derivative.MirabolicProductMinusRightPsi` | `424f4227` | `6cd54f76-f453-4faa-818a-5843e1bbcaff` |
| `Representation.Derivative.MirabolicProductRestriction` | `d58e34da` | `a1d00661-0059-45f4-9f7c-3c6b3cf1af3a` |
| `Representation.Derivative.RightMixedProductDerivativeFiltrationProof` | `dbad7979` | `3231134e-a443-44f4-abda-39c3b5829f76` |
| `Representation.Filtration.FiniteFamilyMultiplicityProof` | `3e121bcb` | `c9dbd607-82e5-4821-b367-736e876565d9` |
| `Representation.Filtration.GradedRefinementProof` | `a6b9aa29` | `8f135e79-b688-4075-b8e6-b05a81a36883` |
| `Representation.Filtration.IntervalLiftProof` | `f47e01a0` | `58e0544d-0db2-42f5-8d39-79d38ff5e2cd` |
| `Representation.Filtration.IrreducibleMultiplicityProof` | `785e7c85` | `9f88af41-d438-475e-ae54-6ef33bcfb8ed` |
| `Representation.Filtration.JordanHolderComparisonProof` | `93052369` | `b43fcaf9-8be5-4717-a87b-a84c667efcbe` |
| `Representation.Filtration.JordanHolderProof` | `dac710c1` | `b43fcaf9-8be5-4717-a87b-a84c667efcbe` |
| `Representation.Filtration.JordanHolderTransportProof` | `763c2ca6` | `77ffbd6e-17db-4751-8dee-c6dcb3b92e09` |
| `Representation.Filtration.LengthCriterionProof` | `6b07cbb0` | `8520a63d-88a5-45e7-adef-84849528ad9d` |
| `Representation.Filtration.LengthTwoMatching` | `701ca674` | `53969569-6b54-45b3-a1f8-89f1fe96a1f8` |
| `Representation.Filtration.MultiplicityIndependenceProof` | `619455f4` | `9f88af41-d438-475e-ae54-6ef33bcfb8ed` |
| `Representation.Filtration.MultiplicityTransportProof` | `1905b374` | `b8ecf398-d8ff-48bd-a6b3-5da6557b7655` |
| `Representation.Filtration.QuasicuspidalVanishingProof` | `43dadb08` | `f64cd5e8-5f73-41c5-9bb0-d59279ffdcee` |
| `Representation.Filtration.SubsingletonProof` | `37e5a059` | `f64cd5e8-5f73-41c5-9bb0-d59279ffdcee` |
| `Representation.Filtration.ZeroFactorDeletionProof` | `2813cc17` | `e0f6a21c-44dd-4676-ad49-1656e49573ed` |
| `Representation.Geometric.BlockSixDecomposableProof` | `8e1b278f` | `91670dc7-3166-4d54-b9cb-bcb148f080b5` |
| `Representation.Geometric.BruhatMatrixExistenceProof` | `b5739893` | `f22fde8e-f597-44d0-a53d-290de4c59b2d` |
| `Representation.Geometric.BruhatWeylReflectionProof` | `9d034ed7` | `4ff454dd-caa9-435d-8c9b-bc4ed0d4b415` |
| `Representation.Geometric.ClosedSubgroupMackeyProof` | `ed2e1c45` | `e71f23b6-a9d9-4bc4-9af9-cde7a187ff8b` |
| `Representation.Geometric.CorrectionSubgroupDiagonalHaarProof` | `0d68f886` | `9c98daee-a78a-429a-81dc-4cebbe02dee1` |
| `Representation.Geometric.GeometricLemmaProof` | `f606bb75` | `67ebcf61-3d58-4499-9c0c-c847e90aaeb4` |
| `Representation.Geometric.IntersectionLeviDiagonalCharacterProof` | `8e3722a0` | `1a585c66-e21e-4071-84a0-09a32af9d745` |
| `Representation.Geometric.MonotoneBlocksProof` | `820f0b5d` | `a5db9be0-3f71-4528-89a8-cd92a0c5e411` |
| `Representation.Geometric.OrbitSectionExtensionProof` | `f6feecf9` | `58ca13a3-4bf3-4aaa-8b7d-e8156d189c64` |
| `Representation.Geometric.PadicCorrectionCancellationProof` | `54d42371` | `7e7f9c7b-a0fb-4b6a-9539-2d6b9988a4cc` |
| `Representation.Geometric.PadicParabolicBruhatProof` | `66197c1e` | `b2c9fb09-d2c7-4895-8320-b447e3cc98c6` |
| `Representation.Geometric.ParabolicOrbitJacquetProof` | `520b0e0b` | `18915f54-27ba-4ed6-a6ba-44d2590fd858` |
| `Representation.Geometric.ParabolicSupportGradedProof` | `62ae1acc` | `1e160a16-f7f4-4d17-b9ee-4fd2e6e0fb34` |
| `Representation.Geometric.ParabolicSupportJacquetProof` | `b5caf4af` | `1e160a16-f7f4-4d17-b9ee-4fd2e6e0fb34` |
| `Representation.Geometric.StandardIntersectionsProof` | `454f2f13` | `5f658ba6-5c6d-46e0-a5c1-6d15317f8a1d` |
| `Representation.Geometric.WeylMinimalRepresentativeProof` | `be673197` | `6e35399b-9029-438e-9663-5ce96ab02576` |
| `Representation.Geometric.WeylUniquenessProof` | `1e54306f` | `9ad51693-f8a1-45de-949a-72d07ecc13b9` |
| `Representation.Hecke.CommonInvarianceProof` | `067a7f86` | `4b135fdc-c234-45a5-99ca-4730d3874d38` |
| `Representation.Induction.CharacterTwistProof` | `9709c7b6` | `fb3e71c3-36c9-4f69-bc65-3572eba2c084` |
| `Representation.Induction.CompactAutomorphismIntegralProof` | `822aed37` | `322d05be-f0c4-46f3-a5ce-0bb0a724e68f` |
| `Representation.Induction.CompactCoinvariantBijectivityProof` | `bd81652f` | `cbaf9d61-f090-41e3-8269-9ae5a6992693` |
| `Representation.Induction.CompactCoinvariantLocalInverseProof` | `a9532713` | `9f55d4f4-ce37-42fa-881d-413bffce13e2` |
| `Representation.Induction.CompactLocalSectionSpanningProof` | `9dda760f` | `0dbbc4e6-1b6c-4682-9e94-bf4b9aa04614` |
| `Representation.Induction.CompactQuotientProof` | `53fcb4f0` | `672038be-3175-4fbd-85a6-d8c272aa63ec` |
| `Representation.Induction.CompactScalarProof` | `ceff0623` | `3d44eb6b-b164-4840-a276-23eef1b3f075` |
| `Representation.Induction.CompactSurjectivityProof` | `0f5c33e5` | `a757e2b6-b764-46f5-8f53-57f3d2d80f9b` |
| `Representation.Induction.CompactTransitivityProof` | `23261764` | `84a052cc-bc16-4936-b3c5-0e50f92ff0a8` |
| `Representation.Induction.FiniteProductTensorBijectiveProof` | `b8bead2c` | `907898cf-8008-4165-a299-db111d558d6f` |
| `Representation.Induction.NormalCoinvariantKernelProof` | `5b05899e` | `89c9c2dc-a112-4cae-b148-3e6de8be0583` |
| `Representation.Induction.NormalCoinvariantProof` | `9a15662a` | `ffe24f57-d375-48bf-b0ef-536f8cea58dd` |
| `Representation.Induction.OppositeProductReversalProof` | `2bdd098e` | `217bc764-94f7-4775-8b6c-eb96939cf3ba` |
| `Representation.Induction.SplitQuotientProof` | `e4355c7e` | `75bc696d-7093-45b4-b951-e84ca3cd5f79` |
| `Representation.Induction.SplitStagesCharacterComparison` | `0bf20b02` | `c4288181-e9d8-4ad2-961d-4d971b1fc625` |
| `Representation.Induction.SurjectivityProof` | `782edcc0` | `63c695c6-3dbd-46f6-b675-f46f1aa2a0bb` |
| `Representation.Jacquet.BlockCompressionProof` | `f43e70ce` | `5e1e7f7b-e604-43bc-abbb-983714e939eb` |
| `Representation.Jacquet.BlockPowerKernelProof` | `17fdf3cd` | `9036bb44-b05d-4c31-a1d2-b0ecc2471985` |
| `Representation.Jacquet.CanonicalLiftBijectivityProof` | `17f84643` | `faf28144-e82d-4543-8ad3-bfab5f2c89e2` |
| `Representation.Jacquet.CanonicalLiftGroupTransportProof` | `0dd3c75e` | `c6b0879c-008f-43a4-b961-7305495342c0` |
| `Representation.Jacquet.CanonicalLiftIntertwinerNaturalityProof` | `fb7dc857` | `9c878f57-a3a7-4cbc-8657-a44eed8c51cf` |
| `Representation.Jacquet.CompactCompressionStableDualityProof` | `c5db14dc` | `fcc707cc-1c32-43d4-a332-42e06ec288b0` |
| `Representation.Jacquet.CompressionStabilizationProof` | `f437baa7` | `d901e340-eb2c-46f2-ae8a-1e041c5dc1b4` |
| `Representation.Jacquet.ExactProof` | `a5d47bfd` | `d30fdbfc-1ea3-4554-9b0f-540abe813aea` |
| `Representation.Jacquet.LocalizationExactnessProof` | `ea6f8b30` | `0574c6f7-8717-4cb2-9498-46220d6b8048` |
| `Representation.Jacquet.OppositeCanonicalLiftProof` | `c28651b0` | `dbae9baf-759b-429d-a685-27521c0b454d` |
| `Representation.Jacquet.ReciprocityProof` | `35b48643` | `21341e99-4de8-4e83-967f-94131828a06d` |
| `Representation.Jacquet.RefinedOppositeCanonicalLiftProof` | `4e155df2` | `9c878f57-a3a7-4cbc-8657-a44eed8c51cf` |
| `Representation.Jacquet.RefinedOppositeCompressionProof` | `19663452` | `9c878f57-a3a7-4cbc-8657-a44eed8c51cf` |
| `Representation.Jacquet.RefinedOppositePowerKernelProof` | `5b5155c6` | `9c878f57-a3a7-4cbc-8657-a44eed8c51cf` |
| `Representation.Jacquet.RefinedOppositeStableImageProof` | `655f10f8` | `9c878f57-a3a7-4cbc-8657-a44eed8c51cf` |
| `Representation.MatrixCoefficient.NormRegularityProof` | `386e3eea` | `c98c74eb-a4cb-4924-8df8-f7556ca47689` |
| `Representation.Parabolic.InverseTransposeProductProof` | `96669dbb` | `fc1a5e69-5e8e-4fcd-ad69-c3d3d1384e91` |
| `Representation.Parabolic.LeviInflationAdmissibilityProof` | `38c8bf1a` | `4c32a273-8e38-4a7c-abb9-f1ad5075ecb9` |
| `Representation.Parabolic.NaturalInductionDualityProof` | `ca3b908f` | `aca46f6c-3494-4a52-aeea-272a8b3fb5f1` |
| `Representation.Parabolic.NaturalJacquetDualityProof` | `67fa0cf2` | `48901b5f-7442-4471-bcb5-95578145d5d4` |
| `Representation.Parabolic.NormalizedAdmissibilityProof` | `c5fb6307` | `440ff377-ae50-452a-b26d-1587b3092538` |
| `Representation.Parabolic.NormalizedJacquetAdmissibilityProof` | `9104334f` | `98f79e48-f457-4ef6-ab80-7be0671d52b0` |
| `Representation.Parabolic.NormalizedJacquetExactnessProof` | `eebdf376` | `9d580fe5-0589-4dfa-9506-1010e413a529` |
| `Representation.Parabolic.OppositeJacquetAdmissibilityProof` | `7461d73d` | `9c878f57-a3a7-4cbc-8657-a44eed8c51cf` |
| `Representation.Parabolic.OppositeRefinementTransitivityProof` | `c9c6b113` | `9f88af41-d438-475e-ae54-6ef33bcfb8ed` |
| `Representation.Parabolic.OrderedProductRegroupingProof` | `3c33bc41` | `2ef80e63-ce40-401c-8203-4cac37fb0307` |
| `Representation.Parabolic.QuotientCompactProof` | `6e7b4c94` | `400d2277-4574-4aea-a50c-da70cb1702f2` |
| `Representation.Parabolic.RefinedInductionTensorProof` | `91b8bcdb` | `fa77b238-a6a2-47ae-9847-87e6de1267de` |
| `Representation.Parabolic.RefinementCoordinatesNormalizationProof` | `31344543` | `77267c3f-9c92-4929-951a-6e6892c89e64` |
| `Representation.Parabolic.RefinementInductionTransitivityProof` | `bce6cf35` | `05a83966-937f-4db1-9195-8ec40311fccd` |
| `Representation.Parabolic.SecondAdjointnessProof` | `4be76e11` | `eb76bbde-911c-4875-9611-a11b9ba0300e` |
| `Representation.Parabolic.StandardOppositeJacquetAdmissibilityProof` | `f3f923d0` | `9c878f57-a3a7-4cbc-8657-a44eed8c51cf` |
| `Representation.Parabolic.UnipotentFiniteContainment` | `bf7f18d2` | `cba1f5ba-df9a-4ee7-a403-baaeebbf4d63` |
| `Representation.RankinSelberg.EqualRankFrobeniusProof` | `1746c825` | `101089c8-6e44-4d3f-b2bf-390f3dc96aff` |
| `Representation.RankinSelberg.GeneralLinearUnimodularity` | `0a2f2e5a` | `0eb4a44f-89d4-473a-bf4f-a7cf2dcaaf9d` |
| `Representation.RankinSelberg.HaarSymmetriesProof` | `b0680b80` | `25af224a-861b-48d6-9a6f-76284babdde5` |
| `Representation.RankinSelberg.LastRowCompactOrbitProof` | `705eefa7` | `8f82e3a6-5ccb-4c0b-b68a-c0e6550c8f4a` |
| `Representation.RankinSelberg.UnipotentUnimodularity` | `e5699c5d` | `4ad92be9-9115-4e7d-b42a-b2adc7dde3e5` |
| `Representation.RankinSelberg.ZeroRowLastRowCutoffProof` | `c1ca32b0` | `06486d65-100f-4e95-b759-bb94e5ff8a98` |
| `Representation.Schur.CountableDimensionProof` | `22a3240d` | `adb98036-1da4-480f-8bac-a97f8173aa1f` |
| `Representation.Smooth.Contragredient.AdmissibleDualityProof` | `81c91e2f` | `a7dd454e-3648-46fd-99db-2029b21d38bb` |
| `Representation.Smooth.Contragredient.ExactProof` | `ed74312b` | `41755c34-9780-45df-88a4-3a7ccd32727e` |
| `Representation.Smooth.Contragredient.GelfandKazhdanProof` | `31571ec8` | `2206daa6-e219-4ed6-9ad1-4f4d47efed93` |
| `Representation.Smooth.Contragredient.HomDualityProof` | `a45dfb51` | `2df2312f-ac71-4f1a-bacb-d4ef2b0d741f` |
| `Representation.Smooth.Contragredient.InvariantPairingProof` | `4e0757e6` | `9c878f57-a3a7-4cbc-8657-a44eed8c51cf` |
| `Representation.Smooth.Factorization.TwoFactorExistenceProof` | `1470f0d7` | `ea7e032e-0818-4425-9fc4-6f30126f4fc4` |
| `Representation.Smooth.Schur.Proof` | `b97b88e5` | `7418b301-258f-4839-83ff-8b508b8a9abd` |
| `Representation.Smooth.SmallRealizationProof` | `b9fc82a3` | `baca19e0-4b51-4368-9b1a-817f6d583c5f` |
| `Representation.Tensor.ExternalMapSurjectivityProof` | `e485a89c` | `c1dbdd67-682c-4d5d-ba6b-43eb6850899b` |
| `Representation.Tensor.SmoothDualInjectivityProof` | `c179611a` | `de802971-5655-401f-a4e8-55e4638699af` |
| `Representation.Tensor.SmoothDualSurjectivityProof` | `b9cdbe70` | `7ad0562a-0aa8-43a6-afcd-6934200e7488` |
| `Representation.Tensor.UnitaryProof` | `373fa4ed` | `f3a2dc88-79d8-4ecf-aaf1-2125d4479a2d` |
| `Representation.Twist.AdmissibilityProof` | `4d0e0b40` | `481101cd-15e1-460d-84f8-3bc4331be8b6` |
| `Representation.Twist.SubquotientProof` | `2b2f7961` | `84b8a0ef-a7b9-4ed9-ab40-1b430d7e0f86` |
| `Representation.Unitary.CentralCharacterProof` | `a1b935a6` | `9c878f57-a3a7-4cbc-8657-a44eed8c51cf` |
| `Representation.Unitary.LeviCuspidalRealUnitarizationProof` | `7fbc2ac8` | `f5b075b2-71a6-407d-8916-4de3b0e9df58` |
| `Representation.Unitary.SquareIntegrableProof` | `5cfbe4bb` | `1559297e-fc4f-49fc-bc37-b7c577c2ba15` |
| `Representation.Unitary.SupercuspidalRealUnitarizationProof` | `ad033912` | `733b7c5a-b9dc-4400-b830-0b91eaadf062` |
| `Representation.Unitary.UnitarizabilityContinuationProof` | `ec26db35` | `7071b052-61cb-4718-babc-684a3e41c288` |
| `Representation.Unramified.SphericalConstituentExistenceProof` | `1ff36e36` | `e2e8da65-f92d-44fa-ac52-7c07e4290054` |
| `Representation.Whittaker.BruhatCellFactorizationProof` | `01bfb9b7` | `c2b0bc2a-c78e-4b75-a659-fee05f37a288` |
| `Representation.Whittaker.BruhatCellInvarianceProof` | `4c108f89` | `40ca3d44-8e3a-40d4-9118-16fcac627174` |
| `Representation.Whittaker.BruhatCellRestrictionVanishingProof` | `2654bbe6` | `db3fb63c-73d8-4983-ae3b-e78a50893941` |
| `Representation.Whittaker.BruhatCellVanishingProof` | `6c2d19dc` | `2c904012-21c7-4439-ac2f-4f6a7e10893d` |
| `Representation.Whittaker.BruhatCompatibleSupportProof` | `591b752d` | `49e92410-96d1-4d78-987c-d3ad6fb6d31b` |
| `Representation.Whittaker.BruhatFiberCharacterCovarianceProof` | `21eb8285` | `74e1dd97-9e58-4212-bcb9-310b35fa3ae3` |
| `Representation.Whittaker.BruhatHaarMeasureProof` | `e9717f96` | `22bc586a-014c-4a50-be9e-bb696f270907` |
| `Representation.Whittaker.BruhatOrbitalIntegrationProof` | `df367457` | `b983acdc-4624-46e6-9453-91a2ceb6bab7` |
| `Representation.Whittaker.CompatibleMonomialFixedProof` | `6e7d99cc` | `262fa24b-c35c-4b90-9e7c-753c3ab85316` |
| `Representation.Whittaker.DistributionInvarianceProof` | `1ffc4346` | `f79ca82c-d050-4ffa-821b-c347b60e36e0` |
| `Representation.Whittaker.GeneralizedCoefficientKernelProof` | `bcf252a5` | `2509ba9f-84e5-486f-b995-7a800b413390` |
| `Representation.Whittaker.MultiplicityOneProof` | `ba2dff22` | `209cde88-bab8-4a85-8a9d-72b8864b6fa0` |
| `Topology.GroupAction.FiniteOrbitProof` | `d152e80f` | `72152240-c606-4fc3-87a0-e6d5972c32fa` |
| `Weil.Representation.ContinuityProof` | `d1c7c679` | `8d52aad7-9f5b-41c1-bf76-c1e6483b9639` |
| `Weil.Representation.IsomorphismInvarianceProof` | `a36e26ca` | `53bd2d23-f25a-4747-9ac9-f82617e20070` |
| `Weil.Representation.OperationClosureProof` | `a6debf58` | `4fa46ac6-ab54-44b7-ab47-ddaa64fbb061` |

The second table lists the 29 further closure modules that prove a named
Library proposition but are not the entry module of a current proof record.
This includes every remaining closure module whose name ends in `Proof`. They
come from the project's first proof rounds, or they are helper modules shipped
with a later proof. "Historical" marks a module that has no proof task in the
current task registry. For such a module the table gives the published
statement and any task that its Markdown names.

| Proved module | Provenance |
| --- | --- |
| `Galois.FiniteField.ComparisonProof` | historical; proves `FrobeniusComparison` (module `Galois.FiniteField.Comparison`); imported by `Weil.Local.Assembly` (supporting unit `3b435643`, task `650de61a-84c3-40d1-b791-0544af5824e1`) |
| `Galois.Local.SpectralProof` | historical; statement artifact `c9ec9a6a-5b72-444a-bfb0-7c5406d5950d` (`SpectralResidueExactness`), proof task `f0e0e8d0-9bed-439a-a648-f7d8d9939d3b` named in its Markdown |
| `Group.GL.Nonarchimedean` | historical; statement module `Group.GL.NonarchimedeanStatement` (`ValuativeGeneralLinearNonarchimedean`) |
| `LocalField.Normalization.Proof` | historical; statement artifact `62e8bb5c-3f54-449e-bbd6-98de9dc15781` (`PadicNormalizationStatement`) |
| `Representation.Compact.ProjectionProof` | historical; statement artifact `91124244-2c99-4f10-91d2-bcab3a34712c`, proof task `849a1dbe-68d3-4bc8-9c67-ca059539e827` named in its Markdown |
| `Representation.Compact.SurjectivityProof` | historical; statement artifact `40e87eae-9077-41b0-a7d0-49e3f58c1d41` |
| `Representation.CuspidalSupport.DeterminantUnitCornerStructureProof` | proves `DeterminantUnitCornerStructureStatement` (BZ76 Lemma 4.9); helper of `CuspidalSupport.CompactCoefficientFinitenessProof` (proof `a23cbcdb`, task `6884361c-0ab2-41b3-8098-9c070c4a1b3e`) |
| `Representation.CuspidalSupport.HarishChandraForwardProof` | helper of `CuspidalSupport.HarishChandraAssembly` (proof `ccad91d6`, task `e28d3ffc-81b2-49c6-a66a-9a344a79e95a`); its theorems take the Cartan decomposition as a hypothesis, which the assembly discharges |
| `Representation.Jacquet.RefinedUpperCanonicalLiftProof` | helper of `Parabolic.NaturalJacquetDualityProof` (proof `67fa0cf2`, task `48901b5f-7442-4471-bcb5-95578145d5d4`); adds no statement |
| `Representation.Jacquet.StablePairingProof` | helper of `Parabolic.NaturalJacquetDualityProof` (same task); adds no statement |
| `Representation.MatrixCoefficient.LawsProof` | historical; statement artifact `e850d833-de95-42c7-acbd-29cdfcad52e7`, task `d472d77b-c3d3-42a4-9ff3-d8acbb94a2d7` named in its Markdown |
| `Representation.Smooth.Admissibility.CofinalProof` | historical; statement artifact `accbe6c3-27d4-43d9-a227-65c4e7b6a993` |
| `Representation.Smooth.Admissibility.EmbeddingProof` | historical; statement artifact `e95c3f58-3ed4-4ddc-b666-462d05ec8cca` (`AdmissibleSubrepresentationStatement`) |
| `Representation.Smooth.Admissibility.EquivalenceProof` | historical; statement artifact `b844a6ce-e7d4-4e71-8bd3-8a80abb57ba0` |
| `Representation.Smooth.Contragredient.CompactDualityProof` | historical; statement `SmoothDualCompactFixedDualityStatement` |
| `Representation.Smooth.Contragredient.LawsProof` | historical; statement artifact `ff1e06de-a5b0-4bc7-81b5-8b4555029cef` |
| `Representation.Smooth.FixedVectors.LawsProof` | historical; statement artifact `d720bdcb-b2b8-4bf6-9b86-31702bea43e6` |
| `Representation.Smooth.FixedVectors.OrderProof` | historical; statement artifact `81e1f095-d4a9-4b4c-ae57-d746ec2fb206` |
| `Representation.Smooth.SmoothPart.BasicProof` | historical; statement artifact `7101568f-3e71-4b9d-b1c5-f35546e0e8dd`, task `3b5e1c81-ba5a-4300-8ff6-27a11ca276e7` named in its Markdown |
| `Representation.Smooth.Transfer.PullbackProof` | historical; statement artifact `f7707f55-9abd-49f4-98e3-d7629f206ee1`, proof task `442dfa1c-e218-4bd4-b7c0-faaccfcf26e7` named in its Markdown |
| `Representation.Smooth.Transfer.SubquotientProof` | historical; statement artifact `b838525e-4b0b-4f85-9085-6f384abedf7a`, proof task `0975ce00-a7a0-4031-a31f-1df98f3afaf3` named in its Markdown |
| `Representation.Twist.AlgebraProof` | historical; statement artifact `2fbcd8fa-9374-4793-bf3b-f0e5a4fbb3d7` |
| `Representation.Twist.ContinuousCharacterProof` | historical; statement artifact `f56acc86-4146-4652-ace8-72cda7a39b7f` (`ContinuousComplexCharacterOpenKernel`), proof task `745f8453-6791-4cc3-91e0-afaf64adb387` named in its Markdown |
| `Representation.Twist.DualProof` | historical; statement artifact `5c831314-e615-411f-9218-bc54346cef78` |
| `Representation.Twist.PullbackProof` | historical; statement artifact `68b9e381-f850-446e-9fa9-4dd178f19481` |
| `Representation.Twist.SmoothProof` | historical; statement artifact `f3828b8f-ac55-4352-955b-9dc9787da742` (`TwistSmoothCompatibility`) |
| `Topology.CompactOpen.NeighborhoodBasis` | historical; statement artifact `25905329-f69e-4866-b0e7-97673395dd3b`, proof task `83c9e2e3-7d24-4ae8-ba36-8fda72b4f789` named in its Markdown |
| `Weil.AlgebraicProof` | historical; statement artifact `a1ca17e7-e6e7-40de-866f-a1db719cc6a2` |
| `Weil.TopologyProof` | historical; statement artifact `9e116c5c-4503-4f92-8dec-62ce6615b117` |

None of the IDs in the second table is among the exclusions. To find these
modules, theorem declarations were scanned for types that are proposition
definitions of a `…Statement` module. The same scan finds only conditional
reductions besides the modules of the two tables: each of them proves a named
proposition from explicit theorem-valued hypotheses. They are
`Classification.NonadjacentLeibnizPieces`, `Classification.NonadjacentTwoBlock`,
`Classification.SegmentEdgeJacquetReduction`,
`Classification.SegmentFullJacquetEdgeData`,
`Classification.TwoSegmentShuffleAssembly`,
`Classification.TwoSupercuspidalAdjacentStructure`,
`CuspidalSupport.AssociatedConditional`,
`CuspidalSupport.CompactCoefficientFinitenessReduction`,
`Derivative.LeftMixedProductHigher`, `Derivative.LeftMixedProductVanishing`,
`Geometric.CosetOrbitOrdering`, `Parabolic.NaturalInductionDualityFromScalar`,
`Parabolic.SecondAdjointnessAssembly` and
`Smooth.Contragredient.GelfandKazhdanAssembly` (all under
`Representation.`). They are not proved inputs on their own. Wherever the
closure uses one of them, a proof module of the first table discharges its
hypotheses with published theorems. The present module discharges the only
hypothesis of `TwoSegmentShuffleAssembly` as described above.

## Development check

`lean_check` in environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f` over Library
commit `fcac121256163a8da6dd01a9483e1104a9b92aba` built this module with no
errors or warnings. Inspection of
`Langlands.Classification.twoSegmentSocleShuffleJacquet` reports a theorem with
level parameters `uF, uV, uW` and axioms `propext`, `Classical.choice` and
`Quot.sound`.
