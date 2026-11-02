# Zelevinsky's Proposition 4.6, step (2)

Author: Worker 1033, first executor of task
`ba6ec030-6fd9-4f87-84f1-0e1e82ae46da`. I wrote this module and the eight
helper modules listed below. Every other input is a published Library
declaration imported by its Lean name. Two helper declarations follow
published code of other authors; the helper Markdown discloses both:

- `QuotientHom.intersectionTransportEquivOne`
  ([LinkedSegmentSocleIdentityPiece](LinkedSegmentSocleIdentityPiece.md)): the
  statement and its `key` step are mine. The rest of the proof is adapted line
  for line from Worker 890's `SegmentEdge.intersectionTransportEquivOf`
  (module `Classification/SegmentEdgeJacquetReduction`, artifact
  `936ff465-c0b4-4e1f-8c8a-ef6139f08699`, task
  `b331611c-526d-4925-87fe-ea67ed6e6fed`).
- `QuotientHom.tprodMap`
  ([LinkedSegmentOverlapAssembly](LinkedSegmentOverlapAssembly.md)): its linear
  map `TensorProduct.map f g` is the one in Worker 837's
  `MixedProductTensor.externalMap` (module `Mirabolic/MixedProducts`, artifact
  `7aa675e1-c7d5-4f42-b6b4-3b5fcd2cdc6c`, task
  `f5488c8d-59a8-4de8-8649-4511bbaea5d9`). That map is for external tensor
  products; the intertwining proof for the internal tensor product here is
  mine.

The helpers import, rather than restate, three other published declarations:
`CuspidalSupport.LeviAdmissibility.index_val`,
`SegmentEdge.subgroupEqualityCompEquiv` and
`SegmentSocleJacquetReduction.compMap`.

## Statement proved

```lean
theorem Langlands.Classification.linkedSegmentSocleReverseProductQuotientHom
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    LinkedSegmentSocleReverseProductQuotientHom.{uF, uV} F T
```

The theorem proves the published proposition
`Langlands.Classification.LinkedSegmentSocleReverseProductQuotientHom.{uF,uV} F T`
of `Langlands.Representation.Classification.LinkedSegmentSocleReverseProductStepsStatement`
(statement artifact `fa568a15-0e47-4b43-9094-80e38892004e`, arrangement task
`7ff2a1e9-89dc-439e-a861-a567b3db92bf`). It does not change the statement pair
or any pair it imports. The outer telescope is exactly
`{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)`, and
there are no other hypotheses. `uF` and `uV` are independent level parameters;
neither is saturated.

The proposition is statement 2 of Zelevinsky 1980, Proposition 4.6 (step (2)
of its proof, printed p. 186), extended to juxtaposed segments. Let `d` be a
two-segment datum with segment-socle blocks, where `Δ' = d.segments 1` precedes
`Δ = d.segments 0`. Let `(U, I)` be any union–intersection replacement and `e`
any socle datum with segment list `U :: I.toList`. Then there is a nonzero
intertwiner `d.induced → e.induced`.

## Proof

The module has two theorems.

`linkedSegmentSocleReverseProductQuotientHom_of h1 h34 h13` derives the
proposition from three hypotheses: step (1) of the same proposition
(`JuxtaposedSegmentSocleReverseProductStructure.{uF, uV} F T`), Ze80 3.4
(`SegmentSocleJacquetFormula.{uF, uV} F T`) and Ze80 Corollary 1.3 in natural
form (`Geometric.PadicIdentityCellQuotientTheorem.{uF, max uF uV}`). The proof
introduces the data and splits on `I`.

- `I = none` (juxtaposed segments): `exists_ne_zero_of_juxtaposed` of
  [LinkedSegmentJuxtaposedCase](LinkedSegmentJuxtaposedCase.md) applies. It
  takes the quotient map onto the top graded piece of the step (1) filtration.
- `I = some J` (overlapping segments): `exists_overlap_split` of
  [LinkedSegmentOverlapSplit](LinkedSegmentOverlapSplit.md) supplies a split
  point `q`. With it, `Δ'.terminal q = J`, while `init = Δ'.initial q`
  precedes `Δ`, is juxtaposed with it, has replacement `(U, none)`, and
  satisfies `deg U = deg Δ + deg init`. Then `exists_ne_zero_of_overlap` of
  [LinkedSegmentOverlapCase](LinkedSegmentOverlapCase.md) gives the nonzero
  intertwiner. It follows Zelevinsky's route: Frobenius reciprocity, the
  identity-cell quotient of the Jacquet module, Ze80 3.4 for `Δ'`, and step
  (1) for `(Δ, init)`.

The main theorem `linkedSegmentSocleReverseProductQuotientHom F T` applies
`linkedSegmentSocleReverseProductQuotientHom_of` to the three published proofs:

- `juxtaposedSegmentSocleReverseProductStructure.{uF, uV} F T` for `h1`;
- `segmentSocleJacquetFormula.{uF, uV} F T` for `h34`;
- `Geometric.padicIdentityCellQuotientTheorem.{uF, max uF uV}` for `h13`.

The overlapping case needs Corollary 1.3 for representations in universe
`max uF uV`, the universe of the blocks of `d`. The published theorem has
independent universe parameters, so this instance is available without
saturating `uV` in the main theorem.

The helper modules, in import order, are:

- [LinkedSegmentSocleIdentityPiece](LinkedSegmentSocleIdentityPiece.md)
- [LinkedSegmentOverlapShapes](LinkedSegmentOverlapShapes.md)
- [LinkedSegmentOverlapInduction](LinkedSegmentOverlapInduction.md)
- [LinkedSegmentOverlapPiece](LinkedSegmentOverlapPiece.md)
- [LinkedSegmentOverlapAssembly](LinkedSegmentOverlapAssembly.md)
- [LinkedSegmentJuxtaposedCase](LinkedSegmentJuxtaposedCase.md)
- [LinkedSegmentOverlapCase](LinkedSegmentOverlapCase.md)
- [LinkedSegmentOverlapSplit](LinkedSegmentOverlapSplit.md)

Their theorems take step (1), Ze80 3.4 and Corollary 1.3 as explicit
hypotheses, where they need them. Only the main theorem of this module
discharges those hypotheses.

## Dependency audit

The imported proved inputs that discharge the three hypotheses are:

| Input | Module | Theorem | Task | Artifact |
| --- | --- | --- | --- | --- |
| Ze80 4.6, step (1) | `Langlands.Representation.Classification.JuxtaposedSegmentSocleReverseProductStructureProof` | `Langlands.Classification.juxtaposedSegmentSocleReverseProductStructure` | `0c90f7e4-78fa-43fd-8736-238bb3e8617d` | `55b6c80e-48c0-41c3-a021-acd3a5c13c1b` |
| Ze80 3.4 | `Langlands.Representation.Classification.SegmentSocleJacquetProof` | `Langlands.Classification.segmentSocleJacquetFormula` | `b95105c6-f8bb-4641-ae53-2f49d1e7f034` | `dbcb1209-e019-4728-b23b-3e10b06ad990` |
| Ze80 Cor. 1.3 | `Langlands.Representation.Geometric.IdentityCellQuotientProof` | `Langlands.Geometric.padicIdentityCellQuotientTheorem` | `eda2d9b9-9151-42cd-9e69-47a82a240f72` | `b7358ead-4ad7-42c6-b074-b46843b41d77` |

The task explicitly allows the step (1) proof. The 3.4 and Corollary 1.3 proofs
are shared lower inputs (Jacquet formula and geometric lemma).

### Every directly imported Library module

The nine modules of this proof import, besides each other, exactly the 24
Library modules below. For each one, the table gives the published artifact
that first contained the module, the kind of that artifact and the task it was
produced for. I read the task from the artifact's publication record: the
review task named there has the producing task as its `host_task_id`.
`OneBlockShape` belongs to the Library seed and has no artifact. The importing
modules are abbreviated: P = this module, I = IdentityPiece, Sh = OverlapShapes,
In = OverlapInduction, A = OverlapAssembly, J = JuxtaposedCase, C =
OverlapCase, Sp = OverlapSplit.

| Library module | Content | Imported by | Artifact (kind) | Task |
| --- | --- | --- | --- | --- |
| `Langlands.Group.GL.OneBlockShape` | single-block shape | I | seed, no artifact | — |
| `Langlands.Representation.Classification.CuspidalIntegralTwistFreenessProof` | proof of integral twist freeness | J, Sp | `a7545313-ab91-4eaf-881e-2ad0d4c58e56` (proof) | `67279e36-f3c2-42e3-9302-11729784042e` |
| `Langlands.Representation.Classification.JuxtaposedSegmentSocleReverseProductStructureProof` | proof of Ze80 4.6 step (1) | P | `55b6c80e-48c0-41c3-a021-acd3a5c13c1b` (proof) | `0c90f7e4-78fa-43fd-8736-238bb3e8617d` |
| `Langlands.Representation.Classification.LanglandsData` | Langlands data for `GL_n` | I | `e6099450-0e93-483c-ad05-c106c269fa72` (definition) | `a7a453ca-879b-4dd7-a07e-bfe49c8e791c` |
| `Langlands.Representation.Classification.LanglandsQuotients` | Langlands quotients and Zelevinsky subrepresentations | J | `a4ca7808-dec9-46ab-b9c5-04c92a2fa2fc` (definition) | `a7a453ca-879b-4dd7-a07e-bfe49c8e791c` |
| `Langlands.Representation.Classification.LinkedSegmentSocleReverseProductStepsStatement` | target statement | J | `fa568a15-0e47-4b43-9094-80e38892004e` (statement) | `7ff2a1e9-89dc-439e-a861-a567b3db92bf` |
| `Langlands.Representation.Classification.ProductLeviCuspidalJacquetAssembly` | product-Levi Jacquet assembly | In | `6c53efc6-946e-43e2-a160-b8973a5dc9f8` (definition) | `74173499-0d59-4f2e-96b3-4fba98114d42` |
| `Langlands.Representation.Classification.SegmentEdgeJacquetReduction` | merged-slot Jacquet filtration | I | `936ff465-c0b4-4e1f-8c8a-ef6139f08699` (definition) | `b331611c-526d-4925-87fe-ea67ed6e6fed` |
| `Langlands.Representation.Classification.SegmentHeadJacquetStatement` | two-block Jacquet modules of segment heads | Sp | `efdabfdc-b9f5-453b-9552-1c321707d7c4` (statement) | `262f1d44-0ca4-44b0-a7ca-8801d8831522` |
| `Langlands.Representation.Classification.SegmentQuotientJacquetSingleBlock` | whole-block Jacquet factorization | I | `34ae0467-49ef-4382-85e7-0a77378c65ef` (definition) | `a91c30bb-d9e7-4f2b-905c-d43996b5e185` |
| `Langlands.Representation.Classification.SegmentReplacementInversions` | the replacement relation `IsUnionIntersectionReplacement` and inversion counts | Sp | `8bbacdd5-ee89-4335-bf69-d21ec69980f6` (definition) | `f3a69bc8-7312-4f82-8a7d-ea3c8188cb63` |
| `Langlands.Representation.Classification.SegmentSocleJacquetProof` | proof of Ze80 3.4 | P | `dbcb1209-e019-4728-b23b-3e10b06ad990` (proof) | `b95105c6-f8bb-4641-ae53-2f49d1e7f034` |
| `Langlands.Representation.Classification.SegmentSocleJacquetReduction` | part of the Ze80 3.4 proof (`compMap`) | A | `dbcb1209-e019-4728-b23b-3e10b06ad990` (proof) | `b95105c6-f8bb-4641-ae53-2f49d1e7f034` |
| `Langlands.Representation.Classification.SegmentSocleJacquetStatement` | Ze80 3.4 statement | I | `aeee25dd-cf01-493b-820d-3bc47ec62b8b` (statement) | `1482a8ae-2e5a-496b-af2d-d79105158b23` |
| `Langlands.Representation.CuspidalSupport.LeviSplitContraction` | Levi block coordinates (`index_val`) | I | `c862f739-656d-4705-89a9-0db3bfc7d716` (proof) | `e1237fc1-de75-4a4d-924b-d509dc475361` |
| `Langlands.Representation.Geometric.GeometricLemmaStatement` | normalized geometric lemma, definitions | I | `47651c73-df4f-4078-9d13-1d4267d9258e` (statement) | `a2a442fc-f72b-43ea-a3f3-bcfd61415ccc` |
| `Langlands.Representation.Geometric.IdentityCellQuotientProof` | proof of Ze80 Cor. 1.3 | P | `b7358ead-4ad7-42c6-b074-b46843b41d77` (proof) | `eda2d9b9-9151-42cd-9e69-47a82a240f72` |
| `Langlands.Representation.Geometric.IdentityCellQuotientStatement` | Ze80 Cor. 1.3 statement | C | `cc17ce3e-9779-48f1-a877-dd12ba29ebe7` (statement) | `704eb687-951c-4c3e-96f1-717ba6d80179` |
| `Langlands.Representation.Geometric.StandardIntersectionsProof` | standard intersections of the geometric lemma | I | `454f2f13-4e58-4601-a2a6-bc94e9c6b6a2` (proof) | `5f658ba6-5c6d-46e0-a5c1-6d15317f8a1d` |
| `Langlands.Representation.Induction.SingleBlock` | single-block normalized induction | I | `fcc278b3-3490-4a69-b2c4-838acdcf9b99` (definition) | `8c397428-6e0f-44f7-b906-d1cf5d652c94` |
| `Langlands.Representation.Parabolic.NaturalFirstAdjointness` | first adjointness | A | `ec16d6b6-be90-4b3d-a6cd-b1ed9bf7f033` (definition) | `eb76bbde-911c-4875-9611-a11b9ba0300e` |
| `Langlands.Representation.Parabolic.RefinedInductionTensorProof` | tensor compatibility of refined induction | I | `91b8bcdb-14ac-4f94-a40c-1ac6a18295ae` (proof) | `fa77b238-a6a2-47ae-9847-87e6de1267de` |
| `Langlands.Representation.Parabolic.RefinedJacquetTensor` | refined Jacquet modules of tensor products | I | `7b878be3-88fe-46c5-841b-ced00776a46e` (definition) | `b752f2bf-57d7-4944-9ef0-3e6fed68e0ac` |
| `Langlands.Representation.Tensor.ProductFiltration` | filtrations of external tensor products | I | `51b5763b-4c87-43e9-81d5-bd1261667959` (definition) | `74173499-0d59-4f2e-96b3-4fba98114d42` |

None of these tasks is among the exclusions, except `f3a69bc8` (socle
exhaustion) for `SegmentReplacementInversions`. The target statement itself
imports that module, so every proof of the target depends on it. It defines
the replacement relation `IsUnionIntersectionReplacement` and proves inversion
counts for it; it does not contain the socle exhaustion result.

### Independence of the whole import closure

All checks are at Library commit `0ebc0efd383ff160084af3b33ab2b7806f7a1dde`.
I followed the `import` lines transitively from this module. The closure has
1182 `Langlands` modules: this module, its eight helpers and 1173 Library
modules.

Check by producing task. For each of the 1173 Library modules I looked up the
first published artifact containing it and that artifact's task, as for the
table above. 17 modules belong to the Library seed and have no artifact. No
module comes from any excluded task except seven modules of task `f3a69bc8`
(socle exhaustion): `Combinatorics.RelationInversions`,
`Classification.SegmentIntegralCoordinates`,
`Classification.SegmentIntervalLinkage`,
`Classification.SegmentReplacementInversions`,
`Classification.SegmentProductReplacement`,
`Classification.SegmentUnionIntersection` and
`Filtration.ObjectTransport`. Each of them lies in the import closure of the
target statement module or of a proof the task permits. The first four are in
the closure of the target statement and of the step (1) proof. The next two
are in the closure of the step (1) proof only. `ObjectTransport` is in the
closures of the step (1) and 3.4 proofs. In particular, no module of task
`a55c4267` (`LinkedSegmentSocleReverseProductStructure`) is in the closure.
An earlier version of `LinkedSegmentJuxtaposedCase` imported
`SegmentPrecedenceTruncation` from that task. It now proves the needed fact
itself (`replacement_eq_of_inter_empty`).

Only five Library modules in the closure lie outside the closures of the
target statement and of the three proofs in the first table. They enter
through two direct imports of my helpers: `LanglandsQuotients` itself, and
`ProductLeviCuspidalJacquetAssembly`, which brings the other three:
`Classification.LanglandsQuotients` (artifact
`a4ca7808-dec9-46ab-b9c5-04c92a2fa2fc`, task
`a7a453ca-879b-4dd7-a07e-bfe49c8e791c`),
`Classification.ProductLeviCuspidalJacquetAssembly` (artifact
`6c53efc6-946e-43e2-a160-b8973a5dc9f8`, task
`74173499-0d59-4f2e-96b3-4fba98114d42`),
`Classification.ProductLeviMinimalIndex` (artifact
`ea634e3b-0543-4509-9bb7-355c72a428e0`, task
`74173499-0d59-4f2e-96b3-4fba98114d42`),
`Classification.ProductLeviCuspidalJacquetMultiplicityStatement` (artifact
`229c454d-d465-40bf-9070-b788325b3f0b`, task
`bb37d5bd-3146-4bc1-be69-02170dca1d8d`) and
`Tensor.FlattenedGLRefinement` (artifact
`c8c667d5-4e53-4e1c-9f8d-cffa601c2d80`, task
`a05d7ed9-95c6-49ed-a77d-a164c0bf4004`). None of these tasks is excluded.

Check by name. I searched all 1182 modules, case-insensitively, for the names
of the excluded propositions and of their proof theorems and modules:

`LinkedSegmentSocleReverseProductStructure`, `LinkedSegmentSoclePairReducible`,
`SegmentSocleProductIrreducibility`, `AdjacentUnlinkedSegmentSocleSwap`,
`TwoSegmentSocleCommutation`, `LinkedSegmentSocleGluing`,
`OrderedMultisegmentSocleExistence`, `MultisegmentSocleExhaustion` (task
f3a69bc8), `SegmentEssentialSquareIntegrableClassification` (aca8805b),
`MultisegmentHeadExhaustion` (3bfb61fa), `OrderedMultisegmentHeadExistence`
(ebea9a8a), `OrderedMultisegmentQuotientExhaustion` (20e4e1c6),
`TemperedBlockUniqueness` (52e97845),
`SquareIntegrableLanglandsClassification`,
`SquareIntegrableLanglandsExhaustion` (cd8ab97c),
`GLRegularLanglandsExhaustion` (bf433f0a) and
`SegmentHeadProductIrreducibility` (8364e73f).

The only matches outside this module are in two statement modules. Both
contain Prop definitions only and no proofs:

- `LinkedSegmentSocleReverseProductStepsStatement`, the target's own statement
  module, mentions `LinkedSegmentSocleReverseProductStructure` in two doc
  comments;
- `RegularLanglandsStatement` defines the proposition
  `GLRegularLanglandsExhaustionStatement` and uses it in the conjunction
  `GLRegularLanglandsQuotientStatement`. No module in the closure proves or
  assumes either one.

So no excluded conclusion, proof successor or proof module is a direct or
transitive dependency. Within the closure, the target
`LinkedSegmentSocleReverseProductQuotientHom` appears only in its statement
module and in this module. In particular, the step (1) proof does not use this
result. Lean reports that the main theorem depends only on the axioms
`propext`, `Classical.choice` and `Quot.sound`.

Derivatives. My modules neither use nor duplicate derivative work. They
contain no derivative construction or derivative argument. The closure
contains 96 modules with `Derivative` in their name: 91 in
`Langlands.Representation.Derivative` and five in `Classification`
(`SupercuspidalDerivativeVanishing`, `SupercuspidalDerivativesProof`,
`SupercuspidalDerivativesStatement`, `SupercuspidalTopDerivative`,
`TwoSupercuspidalDerivativeBridge`). All of them come in through one
published, independently accepted lower input,
`TwoSupercuspidalNonadjacentIrreducibilityProof` (artifact
`98cc1114-db18-414e-8ad5-ddb3f559e47d`). If that module is removed from the
import graph, the closure of this module contains none of them. Its theorem
`twoSupercuspidalNonadjacentProductIrreducible` is Ze80 1.11(a) (task
`3c9849a4-a6c0-43ac-9982-d15ed76bf1e9`, which is not among this task's
exclusions). The step (1) proof imports it directly, and the 3.4 proof imports
it through the Ze80 3.1 proof `SegmentFullJacquetProof` and
`TwoSupercuspidalProductStructureProof`. The Corollary 1.3 proof and my helper
modules import no derivative module. The operator ruled on the same "do not
use or duplicate derivative work" clause in the contract of the step (1) task
(correspondence `35fea30f10ab5d0bad9243914018480c`): the clause governs the
author's own argument and the derivative constructions that Workers 357 and
758 own. It does not exclude published, independently accepted results that
were proved through derivatives. The closure check above covers 1.11(a) and its
whole proof closure.

## Source

A. V. Zelevinsky, *Induced representations of reductive p-adic groups II*,
Ann. Sci. ENS 13 (1980), literature ID `zelevinsky-1980-induced-ii`:
Proposition 4.6 and its proof, steps (1) and (2), printed pp. 185–186;
Proposition 3.4, printed pp. 181–182; Corollary 1.3, printed p. 171. The Lean
proof replaces Zelevinsky's use of 1.5 with the explicit computation of the
identity geometric piece.
