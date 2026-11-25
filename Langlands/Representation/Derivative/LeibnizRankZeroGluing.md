# Complete natural Leibniz filtrations with a rank-zero factor

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
general positive-rank assertion to the full proof
`GeneralLinearDerivativeLeibnizFiltrationProof`.

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

The results below were checked both against the entire import
closure and against these actual mathematical inputs. None of the
following supplies a proof premise, directly or transitively:

| Result not used | Check for this construction |
| --- | --- |
| `UnlinkedSegmentSocleProductIrreducible`, `LinkedSegmentSocleReverseProductStructure`, `LinkedSegmentSoclePairReducible` | No segment-socle product result is in the closure or the quotient/tensor argument. |
| `JuxtaposedSegmentSocleReverseProductStructure`, `LinkedSegmentSocleReverseProductQuotientHom`, and the modules proving them | No reverse-product structure or quotient comparison for segments is used. |
| `SegmentSocleProductIrreducibility` | The argument holds for arbitrary smooth representations and uses no irreducibility criterion. |
| `AdjacentUnlinkedSegmentSocleSwap` and the module proving it | The rank-zero tensor flip is proved by pure tensor algebra; it does not invoke socle commutation. |
| `TwoSegmentSocleCommutation` | No two-segment assertion occurs in the closure or actual inputs. |
| `LinkedSegmentSocleGluing` | The only gluing construction is the generic zero/full one-step filtration, independently proved by quotient algebra. |
| `OrderedMultisegmentSocleExistence`, `MultisegmentSocleExhaustion` | No existence, exhaustion or constituent choice is used. |
| Individual special-head/reverse-socle and segment-socle/reverse-head existence | No head or socle is defined or selected. |
| Analytic segment classification | All comparisons use explicit algebraic maps, not analytic segment classification. |
| `SegmentSpecialEssentialSquareIntegrability` | No square-integrability assertion or analytic criterion is used. |
| Multisegment special-head exhaustion, ordered strong-head existence, quotient coverage, ordered conversion and tempered uniqueness | These classification and existence consumers are absent from the closure. Actual source carriers are retained without decomposition. |
| `GenericSegmentProductUniqueness` | Naturality and singleton enumeration use no uniqueness theorem for generic products. |
| `SquareIntegrableLanglandsClassification`, square-integrable and regular exhaustion | No classification or exhaustion theorem is imported or used. |
| `SegmentHeadProductIrreducibility` | No special-head criterion or its consequences enters the construction. |
| Every segment derivative formula, and segment-socle/head existence or Jacquet formulas | Derivative/tensor commutation is proved from the actual character-localization quotients. No derivative formula for a segment is used. |
| `TwoSupercuspidalNonadjacentProductIrreducible`, `TwoSupercuspidalProductStructure` | The construction does not impose or use supercuspidality, adjacent-product structure or any of these consumer conclusions. |
| `SegmentFullJacquetFormula`, `SegmentHeadJacquetFormula`, `SegmentSocleJacquetFormula`, `SegmentSpecialJacquetExponentNormFormula` | Generic character-localization definitions are used, but none of these segment Jacquet conclusions, their proofs or consequences is in the dependency closure. |
| Ze80 §§3.5, 9.6, 4.2, 9.7, 9.3; classification, exhaustion and unproved BZ77 derivative inputs | No such result or citation is used. The rank-zero comparison and one-step construction are fully proved published inputs. |
| `SupercuspidalCoinvariantFinitenessStatement`; all-character single-block finiteness | Arbitrary `GL_0` carriers and their tensor quotients require no finiteness theorem; that consumer and its consequences are absent. |
| `IrreducibleCoinvariantFinitenessStatement`, `LeviCuspidalCoinvariantFinitenessStatement`, and the mirabolic finite-length route that depends on them | The proof uses no finite-length or Whittaker-finiteness route. No consumer assertion is presumed. |
| The conditional `TwoBlockDerivativePieces` assembly and zero-factor/unit/two-block-shape helpers | These downstream constructions are not imported or used; the comparisons here come from the general published tensor/localization constructions. |

The checks cover mathematical conclusions, the modules proving them and
downstream consequences of the listed results, not only their
identifiers. Proposition definitions in the target module provide the
actual source, pieces and index set; their unproved conclusions are
not hypotheses. The construction uses no unproved statement as
mathematical evidence.
