# Zelevinsky's Proposition 4.6, step (2)

The proof consists of this module and the eight helper modules listed below.
Every other input is a published Library declaration imported by its Lean
name. Two helper declarations follow other published code; the helper
Markdown discloses both:

- `QuotientHom.intersectionTransportEquivOne`
  ([LinkedSegmentSocleIdentityPiece](LinkedSegmentSocleIdentityPiece.md)): the
  statement and its `key` step are written for this proof. The rest of the
  proof is adapted line for line from `SegmentEdge.intersectionTransportEquivOf`
  (module `Classification/SegmentEdgeJacquetReduction`).
- `QuotientHom.tprodMap`
  ([LinkedSegmentOverlapAssembly](LinkedSegmentOverlapAssembly.md)): its linear
  map `TensorProduct.map f g` is the one in
  `MixedProductTensor.externalMap` (module `Mirabolic/MixedProducts`). That map
  is for external tensor products; the intertwining proof for the internal
  tensor product here is written for this proof.

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
of `Langlands.Representation.Classification.LinkedSegmentSocleReverseProductStepsStatement`.
It does not change the statement pair
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

| Input | Module | Theorem |
| --- | --- | --- |
| Ze80 4.6, step (1) | `Langlands.Representation.Classification.JuxtaposedSegmentSocleReverseProductStructureProof` | `Langlands.Classification.juxtaposedSegmentSocleReverseProductStructure` |
| Ze80 3.4 | `Langlands.Representation.Classification.SegmentSocleJacquetProof` | `Langlands.Classification.segmentSocleJacquetFormula` |
| Ze80 Cor. 1.3 | `Langlands.Representation.Geometric.IdentityCellQuotientProof` | `Langlands.Geometric.padicIdentityCellQuotientTheorem` |

The step (1) proof is a permitted input: it does not use this result (see
below). The 3.4 and Corollary 1.3 proofs are shared lower inputs (Jacquet
formula and geometric lemma).

### Every directly imported Library module

The nine modules of this proof import, besides each other, exactly the 24
Library modules below. `OneBlockShape` belongs to the initial Library. The
importing modules are abbreviated: P = this module, I = IdentityPiece, Sh = OverlapShapes,
In = OverlapInduction, A = OverlapAssembly, J = JuxtaposedCase, C =
OverlapCase, Sp = OverlapSplit.

| Library module | Content | Imported by |
| --- | --- | --- |
| `Langlands.Group.GL.OneBlockShape` | single-block shape | I |
| `Langlands.Representation.Classification.CuspidalIntegralTwistFreenessProof` | proof of integral twist freeness | J, Sp |
| `Langlands.Representation.Classification.JuxtaposedSegmentSocleReverseProductStructureProof` | proof of Ze80 4.6 step (1) | P |
| `Langlands.Representation.Classification.LanglandsData` | Langlands data for `GL_n` | I |
| `Langlands.Representation.Classification.LanglandsQuotients` | Langlands quotients and Zelevinsky subrepresentations | J |
| `Langlands.Representation.Classification.LinkedSegmentSocleReverseProductStepsStatement` | target statement | J |
| `Langlands.Representation.Classification.ProductLeviCuspidalJacquetAssembly` | product-Levi Jacquet assembly | In |
| `Langlands.Representation.Classification.SegmentEdgeJacquetReduction` | merged-slot Jacquet filtration | I |
| `Langlands.Representation.Classification.SegmentHeadJacquetStatement` | two-block Jacquet modules of segment heads | Sp |
| `Langlands.Representation.Classification.SegmentQuotientJacquetSingleBlock` | whole-block Jacquet factorization | I |
| `Langlands.Representation.Classification.SegmentReplacementInversions` | the replacement relation `IsUnionIntersectionReplacement` and inversion counts | Sp |
| `Langlands.Representation.Classification.SegmentSocleJacquetProof` | proof of Ze80 3.4 | P |
| `Langlands.Representation.Classification.SegmentSocleJacquetReduction` | part of the Ze80 3.4 proof (`compMap`) | A |
| `Langlands.Representation.Classification.SegmentSocleJacquetStatement` | Ze80 3.4 statement | I |
| `Langlands.Representation.CuspidalSupport.LeviSplitContraction` | Levi block coordinates (`index_val`) | I |
| `Langlands.Representation.Geometric.GeometricLemmaStatement` | normalized geometric lemma, definitions | I |
| `Langlands.Representation.Geometric.IdentityCellQuotientProof` | proof of Ze80 Cor. 1.3 | P |
| `Langlands.Representation.Geometric.IdentityCellQuotientStatement` | Ze80 Cor. 1.3 statement | C |
| `Langlands.Representation.Geometric.StandardIntersectionsProof` | standard intersections of the geometric lemma | I |
| `Langlands.Representation.Induction.SingleBlock` | single-block normalized induction | I |
| `Langlands.Representation.Parabolic.NaturalFirstAdjointness` | first adjointness | A |
| `Langlands.Representation.Parabolic.RefinedInductionTensorProof` | tensor compatibility of refined induction | I |
| `Langlands.Representation.Parabolic.RefinedJacquetTensor` | refined Jacquet modules of tensor products | I |
| `Langlands.Representation.Tensor.ProductFiltration` | filtrations of external tensor products | I |

Of these modules, only `SegmentReplacementInversions` was written in the
development of one of the excluded results listed under "Check by name" below
(socle exhaustion). The target statement itself
imports that module, so every proof of the target depends on it. It defines
the replacement relation `IsUnionIntersectionReplacement` and proves inversion
counts for it; it does not contain the socle exhaustion result.

### Independence of the whole import closure

All checks are at Library commit `0ebc0efd383ff160084af3b33ab2b7806f7a1dde`.
The `import` lines were followed transitively from this module. The closure
has 1182 `Langlands` modules: this module, its eight helpers and 1173 Library
modules.

Check by origin. For each of the 1173 Library modules, the development it was
first written in was looked up. 17 modules belong to the initial Library. No
module comes from the development of an excluded result except seven modules
written for socle exhaustion: `Combinatorics.RelationInversions`,
`Classification.SegmentIntegralCoordinates`,
`Classification.SegmentIntervalLinkage`,
`Classification.SegmentReplacementInversions`,
`Classification.SegmentProductReplacement`,
`Classification.SegmentUnionIntersection` and
`Filtration.ObjectTransport`. Each of them lies in the import closure of the
target statement module or of a permitted proof. The first four are in
the closure of the target statement and of the step (1) proof. The next two
are in the closure of the step (1) proof only. `ObjectTransport` is in the
closures of the step (1) and 3.4 proofs. In particular, no module written in
the development of the proof of `LinkedSegmentSocleReverseProductStructure` is
in the closure. `LinkedSegmentJuxtaposedCase` does not import
`SegmentPrecedenceTruncation`, a module of that development; it proves the
needed fact itself
(`replacement_eq_of_inter_empty`).

Only five Library modules in the closure lie outside the closures of the
target statement and of the three proofs in the first table. They enter
through two direct imports of the helpers: `LanglandsQuotients` itself, and
`ProductLeviCuspidalJacquetAssembly`, which brings the other three:
`Classification.LanglandsQuotients`,
`Classification.ProductLeviCuspidalJacquetAssembly`,
`Classification.ProductLeviMinimalIndex`,
`Classification.ProductLeviCuspidalJacquetMultiplicityStatement` and
`Tensor.FlattenedGLRefinement`. None of them comes from the development of an
excluded result.

Check by name. All 1182 modules were searched, case-insensitively, for the
names of the excluded propositions and of their proof theorems and modules:

`LinkedSegmentSocleReverseProductStructure`, `LinkedSegmentSoclePairReducible`,
`SegmentSocleProductIrreducibility`, `AdjacentUnlinkedSegmentSocleSwap`,
`TwoSegmentSocleCommutation`, `LinkedSegmentSocleGluing`,
`OrderedMultisegmentSocleExistence`, `MultisegmentSocleExhaustion`,
`SegmentEssentialSquareIntegrableClassification`,
`MultisegmentHeadExhaustion`, `OrderedMultisegmentHeadExistence`,
`OrderedMultisegmentQuotientExhaustion`,
`TemperedBlockUniqueness`,
`SquareIntegrableLanglandsClassification`,
`SquareIntegrableLanglandsExhaustion`,
`GLRegularLanglandsExhaustion` and
`SegmentHeadProductIrreducibility`.

The only matches outside this module are in two statement modules. Both
contain Prop definitions only and no proofs:

- `LinkedSegmentSocleReverseProductStepsStatement`, the target's own statement
  module, mentions `LinkedSegmentSocleReverseProductStructure` in two doc
  comments;
- `RegularLanglandsStatement` defines the proposition
  `GLRegularLanglandsExhaustionStatement` and uses it in the conjunction
  `GLRegularLanglandsQuotientStatement`. No module in the closure proves or
  assumes either one.

So no excluded conclusion, proof theorem or proof module is a direct or
transitive dependency. Within the closure, the target
`LinkedSegmentSocleReverseProductQuotientHom` appears only in its statement
module and in this module. In particular, the step (1) proof does not use this
result. Lean reports that the main theorem depends only on the axioms
`propext`, `Classical.choice` and `Quot.sound`.

Derivatives. The nine modules of this proof neither use nor duplicate
derivative work. They contain no derivative construction or derivative
argument. The closure
contains 96 modules with `Derivative` in their name: 91 in
`Langlands.Representation.Derivative` and five in `Classification`
(`SupercuspidalDerivativeVanishing`, `SupercuspidalDerivativesProof`,
`SupercuspidalDerivativesStatement`, `SupercuspidalTopDerivative`,
`TwoSupercuspidalDerivativeBridge`). All of them come in through one
published lower input, `TwoSupercuspidalNonadjacentIrreducibilityProof`. If
that module is removed from the import graph, the closure of this module
contains none of them. Its theorem
`twoSupercuspidalNonadjacentProductIrreducible` is Ze80 1.11(a), which is not
among the excluded results. The step (1) proof imports it directly, and the
3.4 proof imports it through the Ze80 3.1 proof `SegmentFullJacquetProof` and
`TwoSupercuspidalProductStructureProof`. The Corollary 1.3 proof and the
helper modules import no derivative module. The condition "do not use or
duplicate derivative work", which applies to the step (1) proof as well,
governs the argument of the proof itself and the Library's derivative
constructions. It does not exclude published results that were proved through
derivatives. The closure check above covers 1.11(a) and its whole proof
closure.

## Source

A. V. Zelevinsky, *Induced representations of reductive p-adic groups II*,
Ann. Sci. ENS 13 (1980), literature ID `zelevinsky-1980-induced-ii`:
Proposition 4.6 and its proof, steps (1) and (2), printed pp. 185–186;
Proposition 3.4, printed pp. 181–182; Corollary 1.3, printed p. 171. The Lean
proof replaces Zelevinsky's use of 1.5 with the explicit computation of the
identity geometric piece.
