# Highest derivative of an ordered segment-socle product

The theorem `Langlands.Classification.segmentSocleProductHighestDerivative`
proves the unchanged proposition
`Langlands.Classification.SegmentSocleProductHighestDerivative.{uF,uV} F T`
from `Langlands.Representation.Classification.SegmentSocleDerivativesStatement`.
It concerns the actual normalized induction attached to every supplied ordered
segment-product datum with segment-socle blocks.

For the free order `k` equal to the sum of the base ranks, it proves all three
clauses: every higher derivative vanishes; the order-`k` derivative is actually
isomorphic to the induction of an existential datum of end-truncated
nonsingletons in their original order; and the derivative has complex finrank
one when every original segment is a singleton. The output datum has the exact
published `List.ofFn`/`filterMap` equality and `HasSegmentSocles` property.
Repeated or equal segments and arbitrary order are allowed, and no linkage or
nonjuxtaposition condition is imposed.

## Parameters and actual objects

The outer telescope is
`{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)`.
The two universes are independent. Segment bases use `uV`, the field uses `uF`,
and the smooth-representation carriers use `max uF uV`, exactly as in the
published statement. Every construction installs the supplied `T.topology`.

The proof introduces an arbitrary supplied
`ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology`.
This bundled character is continuous and nontrivial; its existence is not an
extra premise. Derivatives are the unchanged
`Derivative.generalLinearDerivative T ψ n k hk`, and products are the actual
normalized induction functors underlying `SegmentProductDatum.induced`.
Vanishing means `Subsingleton` of the actual carrier. The comparison in the
second clause is `Nonempty` of an isomorphism in the smooth-representation
category.

Direct imports are `Classification.SegmentSocleDerivativesProof`,
`Classification.SegmentProductOrderedAssembly`, and
`Derivative.HighestProduct`, all under `Langlands.Representation`.
The only new public declaration is the final theorem. The remaining
declarations in the Lean file are private helpers.

## Implemented proof

Write `D_n^j` for the actual derivative at order `j`, with its explicit bound
proof, and `A × B` for the actual binary normalized product.

### Ordered decomposition and rank transport

The helper `datum_cons` identifies a datum indexed by `Fin (q + 1)` with the
`SegmentProductOrderedAssembly.cons` of its first segment and supplied first
block onto the datum indexed by its successor entries. It eliminates the
segment function and the dependent block function with `Fin.consCases`; the
resulting equality is an equality of the full data records. Consequently the
induction retains the actual blocks, their order and all multiplicities.

Positive segment length gives `Δ.rank ≤ Δ.degree` in `rank_le_degree`.
Summing this inequality and using the datum's degree certificate proves
`rank_sum_le`. These facts provide valid derivative orders for the head and
tail without additional hypotheses.

All rank changes are equality transports. `castRank_eq` identifies the
single-segment statement's `T.castRank` with the published
`generalLinearRankCast` functor. `binaryRankIso` transports the two factor
ranks and their sum; eliminating the rank equalities reduces it to the
identity isomorphism. `omitLine` similarly eliminates a zero head rank and the
ambient-rank equality, then applies the actual categorical isomorphism
`nonempty_iso_omit_left_line`. Its only representation-theoretic hypothesis is
that the rank-zero head has finrank one.

### The cons step

The private proposition `ProductCalculation` packages higher vanishing and
the required existential output datum and isomorphism. Its truncation function
`truncateSegment` is the exact inline function in the published target:
retain `⟨Δ.base, Δ.length - 1, _⟩` when `2 ≤ Δ.length`, and return `none`
otherwise. This packaging is discharged by induction and introduces no
premise into the final theorem.

Suppose the head is `Δ`, its actual socle block is `A`, and the tail datum
`d` has total degree `n` and base-rank sum `s`. Apply the published
`segmentSocleDerivatives F T` to `A`. This gives vanishing above `Δ.rank`,
finrank one at that order when `Δ.length = 1`, and the end-truncated socle
property when `2 ≤ Δ.length`.

The actual comparison `nonempty_cons_iso_binary` identifies the induction of
`cons Δ A d` with `A × d.induced`, including when the tail is empty.
For every order above `Δ.rank + s`,
`HighestProduct.subsingleton_above` combines the head and inductive tail
bounds. Mapping the cons comparison through the derivative and using
injectivity of its underlying equivalence transfers this vanishing to the
original induced representation.

At order `Δ.rank + s`, compose the derivative of the same cons comparison,
`HighestProduct.highestProductIso`, and the binary product of the identity
on the head derivative with the inductive tail isomorphism. The result is an
actual isomorphism to the rank-transported binary product of the head
derivative and the output tail induction.

When `2 ≤ Δ.length`, set
`Δ' = ⟨Δ.base, Δ.length - 1, _⟩`. The identity
`Δ.degree - Δ.rank = Δ'.degree` follows from `Nat.sub_mul`.
Transport the head derivative by this equality and use the single-segment
calculation to prove that the transported block is a socle of `Δ'`.
The output datum is the ambient-rank transport of `cons Δ' A' d'`.
Its socle property follows pointwise from the head and tail properties.
The exact output list follows from `cons_segments`, `List.filterMap_cons`,
and the inductive list equality. Compose `binaryRankIso`, the inverse
output cons comparison, and `rankCast_induced` to obtain the required
isomorphism to this datum's actual induction.

Otherwise positive length forces `Δ.length = 1`, so the head derivative
has rank zero and finrank one. `omitLine` removes this actual rank-zero line
from the binary product. The output datum is the ambient-rank transport of
the tail output alone. The `none` branch of `filterMap` gives its exact
ordered list; rank transport retains its blocks and socle property. Thus
singleton omission is implemented by an actual unit isomorphism.

The binary helper used in this step comes from the actual finite Leibniz
filtration. Above the sum of bounds, every feasible derivative-order pair
exceeds one factor's bound, so every piece vanishes by actual zero-factor
product vanishing. At the sum, every occurrence other than the specified pair
of bounds vanishes. The generic `SingleSurvivingGrade` construction collapses
the actual filtration to that specified graded quotient and composes with its
piece isomorphism. This argument does not assume that the specified piece is
nonzero and does not identify a filtration with a direct sum.

### Length induction and boundary cases

`product_calculation` inducts on the number of entries, with the degree,
datum, free order and rank-sum equality quantified in the induction statement.
For an empty index set, the degree sum forces `n = 0` and the rank sum forces
`k = 0`. No higher valid order exists. The output is the same empty datum,
the list equality is reflexive, its socle property is vacuous, and the
order-zero derivative comparison is the identity isomorphism.

In the successor case, `Fin.sum_univ_succ` splits both degree and base-rank
sums. The tail receives the successor-indexed actual blocks and their supplied
socle proofs. Apply the induction hypothesis at its base-rank sum, then the
cons step. `datum_cons` identifies the constructed cons datum with the input.
The cons comparison already covers an empty tail, so this also proves the
one-entry case.

The final theorem applies this induction at `d.length` and unfolds
`truncateSegment` to the target's exact function. To prove the all-singleton
clause, every original degree equals its base rank, so the degree and rank
sums give `n = k`. The actual isomorphism already constructed transfers
finrank to the output datum at rank `n - k = 0`.
`finrank_zeroDatum`, via the actual empty-product induction/unit isomorphism,
gives finrank one for every such rank-zero datum. This includes the original
empty datum.

## Normalization and sources

The derivative throughout is the published
`Derivative.generalLinearDerivative`, including its determinant inverse-half
normalization. The proof introduces no comparison with a stand-in functor. The
actual Leibniz filtration supplies rank-cast binary normalized products of the
actual factor derivatives. All subsequent operations are evaluation, quotient
collapse, equality transport, induction in stages, or removal of a rank-zero
line, so they preserve that normalization.

The Haar-modulus comparison in the upstream derivative and induction proofs is
proved in `Langlands.Group.GL.MirabolicModulusProof`. Its Lean and Markdown match the fixed
Library base used here. No new normalization assertion is assumed.

The registered originals are:

- A. V. Zelevinsky, *Induced representations of reductive p-adic groups II.
  On irreducible representations of GL(n)* (1980), literature ID
  `zelevinsky-1980-induced-ii`, SHA256
  `663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
  Theorem 3.5 on printed p.182 supplies the single-segment derivative formula;
  the calculation in the proof of Theorem 4.2 on printed p.184 identifies the
  highest derivative of the ordered product with the product of end truncations.
- I. N. Bernstein and A. V. Zelevinsky, *Induced representations of reductive
  p-adic groups I* (1977), literature ID
  `bernstein-zelevinsky-1977-induced-i`, SHA256
  `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
  Lemma 4.5 and Corollary 4.6 on printed p.455 supply the finite Leibniz
  filtration. The Lean proof uses its published actual-filtration
  implementation, rather than replacing a filtration by a direct sum.

The retained files were read at their printed page labels. In the supplied PDF
copies, printed pp.182 and 184 are zero-based indices 18 and 20 (one-based PDF
pages 19 and 21), and printed p.455 is zero-based index 15 (one-based PDF page 16).
No applicable erratum is registered in the supplied literature index or public
source notes. These citations explain the mathematical provenance and proof
route; the Lean inputs below are the proofs used.

## Published proof inputs

| Input | Content |
| --- | --- |
| Exact target statement, `Classification.SegmentSocleDerivativesStatement` | The entire statement import chain is unchanged. |
| `Classification.segmentSocleDerivatives` (Ze80 3.5) | Proved in `Classification.SegmentSocleDerivativesProof`. Its paired page explains the independence audit of that proof. |
| `Derivative.generalLinearDerivativeLeibnizFiltration` | This supplies actual finite subrepresentations and actual graded-quotient isomorphisms, in all ranks including zero. |
| `ObjectRepFiltration.zeroFactorDeletionTheorem` | It deletes the prescribed zero occurrences from the same ambient representation. |
| `objectRepFiltrationSubsingleton` | This includes a zero-length filtration. |
| `ObjectRepFiltration.singleSurvivingGradeIso` | Internal helper. It collapses all but a specified occurrence without assuming that occurrence is nonzero. |
| `Derivative.HighestProduct.highestProductIso` and `subsingleton_above` | Internal helper. Actual binary derivative comparison from the published finite filtration. |
| `Classification.SegmentProductOrderedAssembly` | Internal helper. Actual ordered cons/binary comparison, rank transport, and rank-zero unit operations. |

## Direct and transitive independence

The audit recursively follows every `Langlands` import, including imports used
only for definitions or unused neighboring declarations. It separately records
the external Mathlib and Lean import roots and checks for paired nonempty
Markdown. It compares inherited Lean bytes with the fixed Library base
`df7769b33f1b2e786f8bb0ac3ff1a6fd8a49020e` and reads the published origin of
each added generic construction.

The single-segment proof's recursive closure has 1,178
project modules. Adding the binary highest-derivative and ordered-assembly
helpers gives 1,201 project modules; the final theorem brings the complete
closure to 1,202 project modules and 315 external import roots. All inherited
Lean modules agree with the fixed base. The three additional helper pairs are
`Derivative.HighestProduct`, `Filtration.SingleSurvivingGrade`, and
`Classification.SegmentProductOrderedAssembly`; all six helper files exactly
match the published Library tree at
`7543113c99690e18b45f3b22d252e8cf77c3964e`. The only further pair is this final
proof. No project import or paired Markdown is missing, and the target's entire
recursive imported Lean/Markdown chain is unchanged.

The complete difference from the single-segment proof's closure is the following
23 modules. Names beginning with `Representation.` are relative to `Langlands`.
Each is generic infrastructure or one of the focused helpers of this proof.

| Module | Content |
| --- | --- |
| `Group.GL.HeadTailBlocks` | Consecutive head/tail shapes and exact ordered coordinates. |
| `Representation.Classification.SegmentProductOrderedAssembly` | Ordered cons, rank casts, singleton and empty induction, and rank-zero line removal. |
| `Representation.Classification.SegmentProductSplit` | Actual first-factor/tail induction comparison. |
| `Representation.Derivative.HighestProduct` | The actual binary highest-derivative bound and isomorphism. |
| `Representation.Derivative.ProductVanishing` | Zero-factor vanishing and nonzero-factor induction. Only unconditional `subsingleton_binary` is used here. |
| `Representation.Filtration.SingleSurvivingGrade` | Evaluation and actual collapse to one selected grade. |
| `Representation.Filtration.SingletonIso` | Actual zero/full endpoint quotient isomorphism. |
| `Representation.Induction.EmptyProductUnit` | Actual empty-product induction evaluation. |
| `Representation.Induction.HeterogeneousConstruction` | Induction constructions for independently sized carriers. |
| `Representation.Parabolic.HeadTailProductInduction` | Ordered induction in stages with the singleton factor retained. |
| `Representation.Parabolic.InductionFactorMatchingProof` | Actual induction/finite-filtration factor matching. |
| `Representation.Parabolic.InductionFactorMatchingStatement` | Its proposition definitions. |
| `Representation.Parabolic.InductionSubrepresentation` | Actual induced invariant subspaces. |
| `Representation.Parabolic.OrderedProductRegroupingEquivalence` | Actual representation-equivalence presentation of ordered regrouping. |
| `Representation.Parabolic.ProductInductionSubrepresentation` | Images of supplied tensor-slot subspaces under actual induction. |
| `Representation.Parabolic.ThreeBlockCarrierComparison` | Actual carrier comparisons between the two bracketings. |
| `Representation.Parabolic.ThreeBlockInductionAssociativityStatement` | Generic three-block associativity proposition definition. |
| `Representation.Parabolic.ThreeBlockRefinementGeometry` | Ordered finite refinements and coordinate equalities. |
| `Representation.Parabolic.ThreeBlockRegroupingAssembly` | Composition of actual tensor and induction comparisons. |
| `Representation.Parabolic.ThreeBlockUniverseReduction` | Removal of redundant carrier lifts at the saturated universe. |
| `Representation.Tensor.ExternalFiltration` | Coordinate pullback of a supplied slot filtration. |
| `Representation.Tensor.ExternalSubrepresentation` | Actual external tensor-slot invariant subspaces. |
| `Representation.Tensor.FiniteFiltration` | Indexed tensor equivalences and a supplied-slot filtration. |

Two current Library pairs differ mechanically from their first published versions.
`Tensor.FiniteFiltration` expands `s.equivTransport e` to
`LengthTwo.transport e s`: the former was literally an abbreviation for the
latter in the published `Filtration.ObjectTransport`.
`Parabolic.ThreeBlockRefinementGeometry` replaces its literal one-block shape
with `CuspidalSupport.LeviAdmissibility.oneBlock` from `Group.GL.OneBlockShape`;
the length, constant size, positivity and sum fields are identical. Neither
change imports or introduces a classification conclusion.

The inherited single-segment proof already checks generic modules that belong
to excluded results. Such infrastructure is distinguished from the excluded
mathematical conclusions, and the earlier proof closure, including BZ77 4.7(b),
is used as it is. The same distinction is checked explicitly for
the additional generic modules here:

| Module (relative to `Langlands.Representation`, except `Combinatorics`) | Belongs to | Actual scope |
| --- | --- | --- |
| `Classification.TrivialGroupQuotient` | quotient coverage | Quotient algebra for trivial groups, in the fixed statement chain. |
| `Classification.SegmentProductPermutation` | ordered conversion | Permutation transport for supplied product data, in the statement chain. The final induction preserves the original order. |
| `Classification.OrderedMultisegmentHeadReduction` | ordered special-head existence | Supplied-data reduction and definitions, in the statement chain; no special-head existence theorem. |
| `Classification.SegmentSocleProductData` | socle exhaustion | Segment-product data, in the statement chain. |
| `Classification.SingletonSegmentSocle` | socle exhaustion | The one-segment socle comparison, in the statement chain. |
| `Combinatorics.RelationInversions` | socle exhaustion | Finite list-inversion counting used by earlier independent inputs. |
| `Filtration.ObjectTransport` | socle exhaustion | Pullback and inverse-image transport of supplied actual filtrations. |
| `Classification.CuspidalProductDerivativeQuotientSupport` | support-shift theorem (c) | Quotient form of BZ77 4.7(a), used inside the BZ77 4.7(b) proof; no later support-shift theorem. |
| `Tensor.FiniteFiltration` | socle exhaustion | Generic indexed tensor/slot-filtration algebra; its 19-module closure has no exhaustion theorem. |
| `Filtration.SingletonIso` | `SegmentHeadProductIrreducibility` | Only imports `QuotientFirstIso`; its zero/full endpoint argument uses no special-head criterion. The bundled `TopProduct` module is not imported. |
| `Induction.EmptyProductUnit` | `SegmentHeadProductIrreducibility` | Actual full-subgroup evaluation and empty tensor unit; no special-head conclusion. |

The used `subsingleton_binary` has only the zero-factor premise. No conditional
level theorem in a neighboring bundled module is substituted for an actual
proof of product vanishing.

A comment-stripped scan of the entire closure finds the excluded or later
proposition names only in `Classification.SegmentSocleDerivativesStatement`
and `Classification.MultisegmentClassificationStatement`. These are `Prop`
definitions (including a conjunction of statement definitions), rather than
proofs or supplied hypotheses. In particular the support-shift theorem (c),
its proof module, the special-head criterion, and its derivative proof modules
are absent. The single-segment proof's BZ77 4.7(b) input
uses only the generic quotient-support definition just listed.

| Exclusion, including its proofs and mathematical consequences | Audit result |
| --- | --- |
| `UnlinkedSegmentSocleProductIrreducible` | No conclusion or proof dependency. |
| `LinkedSegmentSocleReverseProductStructure` | No conclusion or proof dependency. |
| `LinkedSegmentSoclePairReducible` | No conclusion or proof dependency. |
| `JuxtaposedSegmentSocleReverseProductStructure` and `LinkedSegmentSocleReverseProductQuotientHom`, with all their proofs | No conclusion or proof dependency. |
| `SegmentSocleProductIrreducibility` | No conclusion or proof dependency. |
| `AdjacentUnlinkedSegmentSocleSwap` | No conclusion or proof dependency. |
| `TwoSegmentSocleCommutation` | No conclusion or proof dependency. |
| `LinkedSegmentSocleGluing` | No conclusion or proof dependency. |
| `OrderedMultisegmentSocleExistence` | Name occurs only in proposition definitions; no proof is used. |
| Socle exhaustion | Only the explicitly listed generic definitions and tensor/filtration lemmas. |
| Segment analytic classification | No conclusion or proof dependency. |
| Special-head multisegment exhaustion | No conclusion or proof dependency. |
| Ordered special-head existence | Only the generic data/reduction module in the fixed statement chain. |
| Quotient coverage | Only generic trivial-group quotient algebra in the fixed statement chain. |
| Ordered conversion | Only supplied-data permutation transport in the fixed statement chain. |
| Tempered block uniqueness | No conclusion or proof dependency. |
| `GenericSegmentProductUniqueness` | No conclusion or proof dependency. |
| `SquareIntegrableLanglandsClassification` | Name occurs only in proposition definitions; no proof is used. |
| Square-integrable exhaustion | No conclusion or proof dependency. |
| Regular exhaustion | No conclusion or proof dependency. |
| Forward special-segment essential square-integrability | No conclusion or proof dependency. |
| `SegmentHeadProductIrreducibility` and its conclusions | Only the generic `SingletonIso` and `EmptyProductUnit` constructions just audited; the criterion and its conclusions are absent. |
| Later support-shift theorem (c), `HighestDerivativeSupportShift`, and later nonjuxtaposed constituent/strict-mono statements (d),(e) | No theorem dependency; only the statement-module proposition definitions are present. |

This audit checks mathematical dependencies. A module that belongs to an
excluded result is not used to import that result's conclusion, and a
statement definition or publication citation is not used as a proof.

## Validation scope

The complete final Lean source has SHA256
`d18191a27a92cd827bfa562d152f404e788d51838fdc11a53029403f9f64d514`.
A check built the helper modules
and final theorem with zero errors and warnings.
Declaration inspection reports independent universe parameters `uF`, `uV`
and only `propext`, `Classical.choice`, and `Quot.sound` as axioms.
The theorem's explicit result is the unchanged published proposition.
