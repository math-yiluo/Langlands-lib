# Complete natural Leibniz filtrations with a rank-zero factor

Author: Worker 593.

This internal helper packages the published natural source-to-piece
comparisons in `LeibnizRankZeroBoundary` as actual one-step filtrations
and complete feasible-index `IsGluedFrom` assertions, when either input
rank is zero. It uses the published generic singleton-filtration
construction in `Filtration.OneStep`.

## Provenance and parameters

This is a derived internal construction. Its mathematical inputs are the
already proved, published natural isomorphisms
`leibnizSourceLeftZeroPieceIso` and `leibnizSourceRightZeroPieceIso`,
the elementary singleton-index lemmas in the same module, and the generic
actual quotient construction in `Filtration.OneStep`. It invokes no further
original-literature theorem. The published rank-zero comparison explains its
relation to the tensor/localization extension of the general derivative
formula; this module performs only the subsequent filtration packaging.

All six declarations are in `Langlands.Derivative`. They have independent
universes `uF` for the supplied `p`-adic field `F` and `uV` for input
representation carriers. The parameters are `{p : ℕ} [Fact p.Prime]`,
`{F : PadicField.{uF} p}`, arbitrary supplied `T : F.TopologicalData`,
and the bundled continuous nontrivial unitary additive character `ψ` for
that topology. In each declaration the topology is installed locally.
The common output carrier universe is `max uF uV`, as in the published
binary product and source functor. No equality between the two universes
or larger-carrier replacement of the inputs is assumed.

Write `S(a,b,d,hd)` for the unchanged
`leibnizSource.{uF,uV} T ψ a b d hd` and `P(a,b,d,x)` for the unchanged
`leibnizPiece T ψ a b d x`. The source is the actual normalized binary
product, then the actual order-`d` general-linear derivative, then
`SmoothRep.toRep`. Each piece uses the two actual factor derivatives,
their normalized binary product and the prescribed smooth rank transport
before forgetting.

## Actual filtrations and their grades

- `leibnizLeftZeroFiltration T ψ b d hd`, for `hd : d ≤ 0 + b`, is
  `RepFunctorFiltration (S(0,b,d,hd)) 1`.
- `leibnizRightZeroFiltration T ψ a d hd`, for `hd : d ≤ a + 0`, is
  `RepFunctorFiltration (S(a,0,d,hd)) 1`.

Both definitions are `RepFunctorFiltration.oneStep` of the literal source.
At every input pair their first subrepresentation is the actual zero
invariant submodule and their last is the actual full invariant submodule
of the source representation. The original source functor maps preserve
both submodules. The actual successive quotient is therefore full modulo
zero; it is not a selected object isomorphic to the source substituted for
that quotient.

- `leibnizLeftZeroGradedIso T ψ b d hd x i`, for
  `x : LeibnizIndex 0 b d` and `i : Fin 1`, identifies the actual grade
  `(leibnizLeftZeroFiltration T ψ b d hd).graded i` naturally with
  `P(0,b,d,x)`.
- `leibnizRightZeroGradedIso T ψ a d hd x i`, for
  `x : LeibnizIndex a 0 d` and `i : Fin 1`, identifies the actual grade
  `(leibnizRightZeroFiltration T ψ a d hd).graded i` naturally with
  `P(a,0,d,x)`.

Each grade isomorphism first applies `oneStepGradedIso` and then the
corresponding published source-to-piece isomorphism. The former is the
first-isomorphism theorem applied to the full-subfunctor inclusion, whose
kernel is zero and whose components are surjective. The latter is a
natural isomorphism of the whole functors on pairs of representations.
Their composition is consequently natural in both inputs and uses the
published rank casts. No extra determinant twist is introduced.

## Complete feasible-index gluing

`generalLinearDerivativeLeibnizFiltration_left_zero T ψ b d hd` proves

```text
∃ e : LeibnizIndex 0 b d ≃ Fin (leibnizIndices 0 b d).card,
  IsGluedFrom S(0,b,d,hd) (fun i => P(0,b,d,e.symm i)).
```

`generalLinearDerivativeLeibnizFiltration_right_zero T ψ a d hd` proves
the same assertion with `(0,b)` replaced by `(a,0)`.

Both proofs choose the finite set's own `Finset.equivFin`. The published
lemmas `leibnizIndices_left_zero hd` and `leibnizIndices_right_zero hd`
identify the entire feasible sets as `{(0,d)}` and `{(d,0)}`,
respectively. Thus their cardinalities are one. The proofs apply
`isGluedFrom_of_length_eq_one` with the source-to-piece isomorphism at
each `e.symm i`. That generic theorem uses the actual one-step filtration
above, with the identity gluing permutation after replacing the length
by one. The exterior enumeration remains an equivalence with the
complete published feasible set; no feasible index is removed.

All orders `d` allowed by `hd` are included. In particular these results
include order zero, the top order and the case where both input ranks
are zero. A representation of `GL_0` retains its arbitrary vector-space
carrier. At top order the unique piece is the actual binary product of
the actual top derivative and the unchanged rank-zero factor; when
both ranks are zero, it is the binary product of the two arbitrary
rank-zero carriers. The constructions require no chosen vector, scalar
identification, finite dimension, finite length, admissibility,
irreducibility, genericity or theorem-valued premise. Zero sources and
zero pieces cause no change to the construction or enumeration.
These declarations prove the two zero-factor cases, and leave the
general positive-rank assertion to the parent proof.

## Direct and transitive import audit

The only direct imports are
`Langlands.Representation.Derivative.LeibnizRankZeroBoundary` and
`Langlands.Representation.Filtration.OneStep`.
Against published Library commit
`2003a7a6a41b5e54c3f790e0887743ed616ed614`, recursive traversal of the
project imports gives 81 dependencies, besides this new module.
Every dependency Lean file and its nonempty paired Markdown file
byte-matches that published tree. The target proposition and every
module it imports are unchanged. The complete project dependency
inventory, grouped by prefix, is:

- `Langlands.Group.GL`: `Basic`, `BlockModulus`, `Blocks`, `Mirabolic`, `MirabolicMixedProductSubgroups`, `MirabolicOppositeIntersection`, `MirabolicProjection`, `MirabolicRadical`, `Nonarchimedean`, `NonarchimedeanStatement`, `NormalizedCharacter`, `OppositeBlocks`, `Padic`, `PadicBlocks`, `RankMaps`, `RankReindex`, `ReindexCongr`, `UpperUnipotent`.
- `Langlands.HarmonicAnalysis`: `Basic`.
- `Langlands.LocalField`: `Canonical`, `Definitions`, `Topology`.
- `Langlands.LocalField.Normalization`: `Definitions`, `Proof`, `Statement`.
- `Langlands.Representation.Category`: `Basic`, `Subquotients`, `Twist`.
- `Langlands.Representation.Derivative`: `GeneralLinearDerivativeLeibnizFiltrationStatement`, `Homogeneity`, `Iteration`, `LeibnizRankZeroBoundary`, `MirabolicCharacter`, `MirabolicMinus`, `RankCastCompat`, `ZeroRankTensor`.
- `Langlands.Representation.Dual`: `Definitions`.
- `Langlands.Representation.Filtration`: `Definitions`, `OneStep`, `QuotientFirstIso`.
- `Langlands.Representation.Induction`: `BinaryProduct`, `BlockFactors`, `Definitions`, `Parabolic`.
- `Langlands.Representation.Jacquet`: `Coinvariants`, `Localization`, `PositiveCharacter`, `SmoothTwist`.
- `Langlands.Representation.MatrixCoefficient`: `Definitions`, `LawsProof`, `LawsStatement`.
- `Langlands.Representation.Mirabolic`: `MixedProducts`.
- `Langlands.Representation.Smooth`: `Definitions`.
- `Langlands.Representation.Smooth.Admissibility`: `CofinalProof`, `CofinalStatement`.
- `Langlands.Representation.Smooth.SmoothPart`: `BasicProof`, `BasicStatement`, `Definitions`.
- `Langlands.Representation.Smooth.Transfer`: `PullbackProof`, `PullbackStatement`, `SubquotientProof`, `SubquotientStatement`.
- `Langlands.Representation.Tensor`: `Finite`, `OneFactor`.
- `Langlands.Representation.Twist`: `AdmissibilityProof`, `AdmissibilityStatement`, `AlgebraProof`, `AlgebraStatement`, `ContinuousCharacterProof`, `ContinuousCharacterStatement`, `Definitions`, `RealPower`, `SmoothProof`, `SmoothStatement`, `SubquotientDefinitions`, `SubquotientProof`, `SubquotientStatement`.
- `Langlands.Representation.Whittaker`: `Algebraic`, `GeneralLinear`.
- `Langlands.Topology`: `CompactNormCharacter`.
- `Langlands.Topology.Nonarchimedean`: `Subgroup`.

The `Whittaker` modules in this list supply elementary functionals and
function models only. The admissibility-named modules provide general
smoothness and twisting infrastructure; their presence does not impose
admissibility on these constructions. No finiteness theorem for
Whittaker coinvariants is imported.

## Mathematical proof-dependency audit

The new proof terms use only `oneStep`, `oneStepGradedIso`,
`isGluedFrom_of_length_eq_one`, the two unconditional source-to-piece
isomorphisms, the two singleton-index lemmas, `Finset.equivFin`,
singleton cardinality and composition of natural isomorphisms.
The generic filtration constructions reduce to invariant submodules,
quotients and the first-isomorphism theorem. In the rank-zero comparison,
the source-to-piece isomorphisms reduce to the published tensor models
of binary products with a zero factor, character-localization quotient
maps `[v ⊗ w] ↦ [v] ⊗ w` and their explicit inverses, tensor symmetry,
functorial restriction/twisting and equality-based rank transport.
There is no appeal to a general derivative filtration, to an unproved
restriction sequence, or to exactness of a minus functor.

The inherited exclusions were checked both against the entire import
closure and against these actual mathematical inputs. None of the
following supplies a proof premise, directly or transitively:

| Inherited condition | Check for this construction |
| --- | --- |
| `UnlinkedSegmentSocleProductIrreducible`, `LinkedSegmentSocleReverseProductStructure`, `LinkedSegmentSoclePairReducible`; tasks `23e98d90-6055-4e35-91a9-b0f5d8a84961`, `a55c4267-7e3a-43f6-8bb1-ce319e1d0aa9`, `8fa9f68b-fa1b-431a-97f6-5b163964d1fc` | No segment-socle product result is in the closure or the quotient/tensor argument. |
| `JuxtaposedSegmentSocleReverseProductStructure`, `LinkedSegmentSocleReverseProductQuotientHom`; task `7ff2a1e9-89dc-439e-a861-a567b3db92bf` and successors | No reverse-product structure or quotient comparison for segments is used. |
| `SegmentSocleProductIrreducibility`; task `2ae5cbe5-0701-4509-88a0-db8cbeb35be4` | The argument holds for arbitrary smooth representations and uses no irreducibility criterion. |
| `AdjacentUnlinkedSegmentSocleSwap`; tasks `e3634665-571b-4852-9f4c-bab8a1053434`, `cded83f3-df9c-4018-bc61-dc54f5c1f9ab` | The rank-zero tensor flip is proved by pure tensor algebra; it does not invoke socle commutation. |
| `TwoSegmentSocleCommutation`; tasks `426911b4-6620-413f-8065-04b25287f3bd`, `66e3b87c-647e-41e4-af18-df4d436765f0` | No two-segment assertion occurs in the closure or actual inputs. |
| `LinkedSegmentSocleGluing`; tasks `c84cd52c-3ff3-4024-be50-8b84dd480888`, `6780b79c-9526-46aa-b8b4-00377d68b1ea` | The only gluing construction is the generic zero/full one-step filtration, independently proved by quotient algebra. |
| `OrderedMultisegmentSocleExistence`, `MultisegmentSocleExhaustion`; tasks `23189526-80b0-4828-a6d4-7ebec2cbeef5`, `f3a69bc8-7312-4f82-8a7d-ea3c8188cb63` | No existence, exhaustion or constituent choice is used. |
| Individual special-head/reverse-socle and segment-socle/reverse-head existence; tasks `67279e36-f3c2-42e3-9302-11729784042e`, `4ca79bbd-589e-476b-9f65-661e799984b5` | No head or socle is defined or selected. |
| Analytic segment classification; task `aca8805b-054f-4d56-8045-12db7f623404` | All comparisons use explicit algebraic maps, not analytic segment classification. |
| `SegmentSpecialEssentialSquareIntegrability`; task `5eece9e8-7f6b-4ea9-abea-a1f9f1b8c807` | No square-integrability assertion or analytic criterion is used. |
| Multisegment special-head exhaustion, ordered strong-head existence, quotient coverage, ordered conversion and tempered uniqueness; tasks `3bfb61fa-1129-4fc9-83fd-7fcfec22106e`, `ebea9a8a-9b21-4208-aa31-98c2dea1f8a3`, `20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584`, `8252833d-c269-41a9-824c-5879e531b23b`, `52e97845-36bb-457d-b76f-70753334b88c` | These classification and existence consumers are absent from the closure. Actual source carriers are retained without decomposition. |
| `GenericSegmentProductUniqueness`; task `30341ae4-65f2-4a0e-9283-763db01a409e` | Naturality and singleton enumeration use no uniqueness theorem for generic products. |
| `SquareIntegrableLanglandsClassification`, square-integrable and regular exhaustion; tasks `1cb45da2-7007-4351-a694-594fb148b8d1`, `cd8ab97c-0b78-4bce-97c4-d307a28159a4`, `bf433f0a-921a-428c-b0c0-6475438125ac` | No classification or exhaustion theorem is imported or used. |
| `SegmentHeadProductIrreducibility`; task `8364e73f-14ec-4d14-8f2b-1555a7c1ce95` | No special-head criterion or its consequences enters the construction. |
| Every segment derivative formula, parent contribution parts (b), (d), (e), (f), and segment-socle/head existence or Jacquet formulas | Derivative/tensor commutation is proved from the actual character-localization quotients. No derivative formula for a segment is used. |
| `TwoSupercuspidalNonadjacentProductIrreducible`, `TwoSupercuspidalProductStructure`; tasks `3c9849a4-a6c0-43ac-9982-d15ed76bf1e9`, `ab61f565-1427-4746-ba77-46097563e962` | The construction does not impose or use supercuspidality, adjacent-product structure or any of these consumer conclusions. |
| `SegmentFullJacquetFormula`, `SegmentHeadJacquetFormula`, `SegmentSocleJacquetFormula`, `SegmentSpecialJacquetExponentNormFormula`; tasks `ed48ae06-964c-4c84-9e62-978f5a953ca7`, `55ad1e10-62d8-46b7-a081-909ef0056426`, `b95105c6-f8bb-4641-ae53-2f49d1e7f034`, `92aea10f-62ac-4e0b-bd4a-9a80909797c5` | Generic character-localization definitions are used, but none of these segment Jacquet conclusions, successors or consequences is in the dependency closure. |
| Ze80 §§3.5, 9.6, 4.2, 9.7, 9.3; classification, exhaustion and unproved BZ77 derivative inputs | No such result or citation is used. The rank-zero comparison and one-step construction are fully proved published inputs. |
| `SupercuspidalCoinvariantFinitenessStatement`; all-character single-block task `62de5903-b616-4b5c-88eb-a066b77c5467` | Arbitrary `GL_0` carriers and their tensor quotients require no finiteness theorem; that consumer and its consequences are absent. |
| `IrreducibleCoinvariantFinitenessStatement`, `LeviCuspidalCoinvariantFinitenessStatement`; tasks `5ab445dc-d2b4-4072-80d1-6370870a4a26`, `3ff5c8fb-397c-4345-bcb3-5d98a0993d18`, and the unrepaired mirabolic finite-length route `5428fe2c-013c-482d-aa6e-7df43e7191aa` | The proof uses no finite-length or Whittaker-finiteness route. No repair, pending proof or consumer assertion is presumed. |
| Worker 745's conditional `TwoBlockDerivativePieces` assembly and zero-factor/unit/two-block-shape helpers | These downstream constructions are not imported or used; the comparisons here come from the general published tensor/localization constructions. |

The checks cover mathematical conclusions, proof successors and
downstream consequences of the listed exclusions, not only their
identifiers. Proposition definitions in the target module provide the
actual source, pieces and index set; their unproved conclusions are
not hypotheses. The construction uses neither a private draft nor a
pending proof as mathematical evidence, and does not contact or rely on
work from the paused Worker 127.
