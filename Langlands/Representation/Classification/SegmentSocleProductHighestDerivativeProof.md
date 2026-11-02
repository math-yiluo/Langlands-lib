# Highest derivative of an ordered segment-socle product

Authors: Worker 593 (ordered assembly and exact induction) and Worker 508
(binary highest-derivative calculation, source and dependency verification).
Task: `4e152d19-e9d0-4cb4-b2c8-6dcc7f7fe21d`, revision 1.

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
independently proved by `Langlands.Group.GL.MirabolicModulusProof`, artifact
`f25fdd6c-d842-40be-b220-92bda8715865`, proof task
`f947a735-872d-44db-a9ea-954d17dec4bd`, Reviewer 4063, published at
`cb6a47b2390bdcd0be78fac0552b7fd5c46cd51b`. Its Lean and Markdown match the fixed
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
  filtration. The Lean proof uses its independently published actual-filtration
  implementation, rather than replacing a filtration by a direct sum.

The retained files were read at their printed page labels. In the supplied PDF
copies, printed pp.182 and 184 are zero-based indices 18 and 20 (one-based PDF
pages 19 and 21), and printed p.455 is zero-based index 15 (one-based PDF page 16).
No applicable erratum is registered in the supplied literature index or public
source notes. These citations explain the mathematical provenance and proof
route; the Lean inputs below are the proofs used.

## Published proof inputs

| Input | Independent publication evidence |
| --- | --- |
| Exact target statement, `Classification.SegmentSocleDerivativesStatement` | Statement artifact `c27c6879-9906-43fa-8d88-cf1808b55f2d`, Reviewer 4178, commit `c76b7751d5e9d82df7a4e5d57684adcee5d41cb7`, integration `3204e509b7804cf79bb5282fef637f6e`. The entire statement import chain is unchanged. |
| `Classification.segmentSocleDerivatives` (Ze80 3.5) | Proof artifact `ac220f41-e7d4-4c9f-951f-0ff12e51412f`, task `209027ca-f49c-472a-af2a-f2fc0006950e`, commit `e530d1eb7e66b0d2b988684aaaa90a729bda10e2`, integration `b202a6bd07dc4fecbfe8d38e0ef25a56`. Its paired proof explains the earlier-unit independence audit. |
| `Derivative.generalLinearDerivativeLeibnizFiltration` | Proof artifact `c4c5439d-5c26-42e5-848a-0f199ce34f7d`, commit `e3944f764d2c00d53ac87227e98601bb667f348f`, integration `2e2f22e103a24ab2b83d08b5bbf1108f`. This supplies actual finite subrepresentations and actual graded-quotient isomorphisms, in all ranks including zero. |
| `ObjectRepFiltration.zeroFactorDeletionTheorem` | Proof artifact `2813cc17-8241-4b38-b9f6-da8e3af69fe2`, commit `9488f8128fc175e4f17b08d2a86eac54056fa753`, integration `bf5309d6bc0c478a8dcf1efcbeca743d`. It deletes the prescribed zero occurrences from the same ambient representation. |
| `objectRepFiltrationSubsingleton` | Proof artifact `37e5a059-7154-47ff-916c-8083f9ea8dc7`, task `f64cd5e8-5f73-41c5-9bb0-d59279ffdcee` revision 2, Reviewer 733, commit `2f8d1873fbaeb581719bc35dbf6f5c9f2d4a8df4`, integration `37b87728c253479fbeef462886256c5a`. This includes a zero-length filtration. |
| `ObjectRepFiltration.singleSurvivingGradeIso` | Internal helper artifact `f5b2b8c3-6e89-4ca0-add4-b39994e58928`, Reviewer 9188, commit `7a2e42fd31831029d34cafb155ffad911920df25`, integration `5c502a4410ae4c9bb63861094e63898e`. It collapses all but a specified occurrence without assuming that occurrence is nonzero. |
| `Derivative.HighestProduct.highestProductIso` and `subsingleton_above` | Internal helper artifact `a45a115f-22a4-47a9-8272-c5f188bca767`, Reviewer 9201, review `89d34120-6d6a-4528-a05a-333a0af0d8a5`, commit `7543113c99690e18b45f3b22d252e8cf77c3964e`, integration `4816c773317445a39bb29f41c8dad797`. Actual binary derivative comparison from the published finite filtration. |
| `Classification.SegmentProductOrderedAssembly` | Internal helper artifact `7eb3979e-27f3-4acc-b2e1-b14899167792`, Reviewer 9198, review `48767f8f-00ed-4ec4-9a3a-12b618356020`, commit `7543113c99690e18b45f3b22d252e8cf77c3964e`, integration `d28957770cd14d29939007c9b4e4d8e8`. Actual ordered cons/binary comparison, rank transport, and rank-zero unit operations. |

## Direct and transitive independence

The audit recursively follows every `Langlands` import, including imports used
only for definitions or unused neighboring declarations. It separately records
the external Mathlib and Lean import roots and checks for paired nonempty
Markdown. It compares inherited Lean bytes with the fixed Library base
`df7769b33f1b2e786f8bb0ac3ff1a6fd8a49020e` and reads the published origin and
independent review for added generic constructions. Whole-workspace snapshots
are not treated as ownership: an origin is an artifact's entry pair or an
auxiliary pair explicitly included in its review.

The already accepted single-segment proof's recursive closure has 1,178
project modules. Adding the binary highest-derivative and ordered-assembly
helpers gives 1,201 project modules; the final theorem brings the complete
closure to 1,202 project modules and 315 external import roots. All inherited
Lean modules agree with the fixed base. The three additional helper pairs are
`Derivative.HighestProduct`, `Filtration.SingleSurvivingGrade`, and
`Classification.SegmentProductOrderedAssembly`; all six helper files exactly
match the independently published Library tree at
`7543113c99690e18b45f3b22d252e8cf77c3964e`. The only further pair is this final
proof. No project import or paired Markdown is missing, and the target's entire
recursive imported Lean/Markdown chain is unchanged.

The complete difference from the single-segment proof's closure is the following
23 modules. Names beginning with `Representation.` are relative to `Langlands`.
Each is generic infrastructure or one of this task's focused helpers.

| Module | Content / independently reviewed origin |
| --- | --- |
| `Group.GL.HeadTailBlocks` | Consecutive head/tail shapes and exact ordered coordinates; `621da62e-8f67-4d7f-8f56-bcad451f2735`. |
| `Representation.Classification.SegmentProductOrderedAssembly` | Ordered cons, rank casts, singleton and empty induction, and rank-zero line removal; `7eb3979e-27f3-4acc-b2e1-b14899167792`. |
| `Representation.Classification.SegmentProductSplit` | Actual first-factor/tail induction comparison; grouped and reviewed in `5440c02b-fc2d-4abe-bbe8-6cd061c6a683`. |
| `Representation.Derivative.HighestProduct` | The actual binary highest-derivative bound and isomorphism; `a45a115f-22a4-47a9-8272-c5f188bca767`. |
| `Representation.Derivative.ProductVanishing` | Zero-factor vanishing and nonzero-factor induction; grouped in `6ded142e-bf04-4d18-8956-a5850e80410b`. Only unconditional `subsingleton_binary` is used here. |
| `Representation.Filtration.SingleSurvivingGrade` | Evaluation and actual collapse to one selected grade; `f5b2b8c3-6e89-4ca0-add4-b39994e58928`. |
| `Representation.Filtration.SingletonIso` | Actual zero/full endpoint quotient isomorphism; grouped in `3ee88231-270b-4cee-8670-915e76b64f12`. |
| `Representation.Induction.EmptyProductUnit` | Actual empty-product induction evaluation; `273c225f-7fb3-4cf4-852c-88d7816b0bae`. |
| `Representation.Induction.HeterogeneousConstruction` | Induction constructions for independently sized carriers; `9d2b0d07-09b8-4c96-92ab-7e5a1e780a02`. |
| `Representation.Parabolic.HeadTailProductInduction` | Ordered induction in stages with the singleton factor retained; `665edfad-042c-4845-bf51-ff72c2267442`. |
| `Representation.Parabolic.InductionFactorMatchingProof` | Actual induction/finite-filtration factor matching; `91f99d8f-f20e-4a65-803f-2ca4409cf984`. |
| `Representation.Parabolic.InductionFactorMatchingStatement` | Its proposition definitions; `e7947b21-e669-45f0-bcfa-60a3668194b6`. |
| `Representation.Parabolic.InductionSubrepresentation` | Actual induced invariant subspaces; `305bd86b-670e-4369-ab5a-549ec74ee689`. |
| `Representation.Parabolic.OrderedProductRegroupingEquivalence` | Actual representation-equivalence presentation of ordered regrouping; `cc3afd44-2cb4-446c-9c09-99f8195d3790`. |
| `Representation.Parabolic.ProductInductionSubrepresentation` | Images of supplied tensor-slot subspaces under actual induction; `fec3f86b-c0ba-42b2-b6b7-bb31421a8b56`. |
| `Representation.Parabolic.ThreeBlockCarrierComparison` | Actual carrier comparisons between the two bracketings; `c2ccdc2a-8bce-478d-8f11-95a328d1730a`. |
| `Representation.Parabolic.ThreeBlockInductionAssociativityStatement` | Generic three-block associativity proposition definition; `e58a7a2f-c633-4435-9f1d-460c7488e62b`. |
| `Representation.Parabolic.ThreeBlockRefinementGeometry` | Ordered finite refinements and coordinate equalities; `0dc591e2-ca9b-4973-ab30-a8097a84ef84`. |
| `Representation.Parabolic.ThreeBlockRegroupingAssembly` | Composition of actual tensor and induction comparisons; `dcd3e87b-e03d-4590-aead-b78a75d70d92`. |
| `Representation.Parabolic.ThreeBlockUniverseReduction` | Removal of redundant carrier lifts at the saturated universe; `e1b47249-7d22-4ff5-9c45-f3fbd6420a4b`. |
| `Representation.Tensor.ExternalFiltration` | Coordinate pullback of a supplied slot filtration; `428f73bc-5621-43c2-b72b-3aed5f40320c`. |
| `Representation.Tensor.ExternalSubrepresentation` | Actual external tensor-slot invariant subspaces; `6ddf89c2-bf68-48c5-bb80-7b620f4af522`. |
| `Representation.Tensor.FiniteFiltration` | Indexed tensor equivalences and a supplied-slot filtration; `1529e866-4b41-41d6-9510-5b00eacdd1c7`. |

Two current Library pairs differ mechanically from their original publications.
`Tensor.FiniteFiltration` expands `s.equivTransport e` to
`LengthTwo.transport e s`: the former was literally an abbreviation for the
latter in the published `Filtration.ObjectTransport`. Its original independent
acceptance is Reviewer 3131, commit
`4bc9613163fd74b82bed79403a0abfa2617a007d`, integration
`13b936d3f92b4cd8a41cc2bb51936124`.
`Parabolic.ThreeBlockRefinementGeometry` replaces its literal one-block shape
with `CuspidalSupport.LeviAdmissibility.oneBlock` from `Group.GL.OneBlockShape`;
the length, constant size, positivity and sum fields are identical. Its original
publication is `65f39f42712a45624ccc76ac5da7b60f52ebcd6f`, integration
`7327da5d4e5343ef851fd282f3be3394`. Neither change imports or introduces a
classification conclusion.

The inherited single-segment proof already checks generic modules published
under excluded programs. The operator's responses
`2b34e4035a5b5dafad7ad84d5a8c0dd8` and
`10df3136f50c5901b1061d52c6b92e07` distinguish such infrastructure from the
excluded mathematical conclusions and permit the disclosed earlier proof
closure, including BZ77 4.7(b). The same distinction is checked explicitly for
the additional generic modules here:

| Module (relative to `Langlands.Representation`, except `Combinatorics`) | Artifact / publishing task | Actual scope |
| --- | --- | --- |
| `Classification.TrivialGroupQuotient` | `1e56ed7e-1297-4655-9b05-0b7e49883863` / `20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584` | Quotient algebra for trivial groups, in the fixed statement chain. |
| `Classification.SegmentProductPermutation` | `0095a4c4-eb6a-411f-8c24-e46a92b21b2b` / `8252833d-c269-41a9-824c-5879e531b23b` | Permutation transport for supplied product data, in the statement chain. The final induction preserves the original order. |
| `Classification.OrderedMultisegmentHeadReduction` | `6529dc85-0346-4e15-9152-54cb47d3528f` / `ebea9a8a-9b21-4208-aa31-98c2dea1f8a3` | Supplied-data reduction and definitions, in the statement chain; no special-head existence theorem. |
| `Classification.SegmentSocleProductData` | `29cea4fd-c41f-4137-8e97-14ab0cdf8d71` / `f3a69bc8-7312-4f82-8a7d-ea3c8188cb63` | Segment-product data, in the statement chain. |
| `Classification.SingletonSegmentSocle` | `8aac8ad9-4364-4514-af9e-e52f99707dfd` / `f3a69bc8-7312-4f82-8a7d-ea3c8188cb63` | The one-segment socle comparison, in the statement chain. |
| `Combinatorics.RelationInversions` | `9e971abc-0144-4575-8205-89a2ae397e63` / `f3a69bc8-7312-4f82-8a7d-ea3c8188cb63` | Finite list-inversion counting used by earlier independent inputs. |
| `Filtration.ObjectTransport` | `68054cb0-7541-498d-bd52-0414519d5815` / `f3a69bc8-7312-4f82-8a7d-ea3c8188cb63` | Pullback and inverse-image transport of supplied actual filtrations. |
| `Classification.CuspidalProductDerivativeQuotientSupport` | `bf38b454-70f8-4bf4-83b2-0def96b608a0` / `f81d9b36-2615-4fec-abc2-50ef93d880bf` | Quotient form of BZ77 4.7(a), used inside the permitted BZ77 4.7(b) proof; no later support-shift theorem. |
| `Tensor.FiniteFiltration` | `1529e866-4b41-41d6-9510-5b00eacdd1c7` / `f3a69bc8-7312-4f82-8a7d-ea3c8188cb63` | Generic indexed tensor/slot-filtration algebra; its independently reviewed 19-module closure has no exhaustion theorem. |
| `Filtration.SingletonIso` | `3ee88231-270b-4cee-8670-915e76b64f12` / `8364e73f-14ec-4d14-8f2b-1555a7c1ce95` | Only imports `QuotientFirstIso`; its zero/full endpoint argument uses no special-head criterion. Reviewer 7943, commit `aa1400a0eb858f7fdc607a5bb736d8f7a705fa10`, integration `2e375c7827024fd992865fca143991fd`. The bundled `TopProduct` module is not imported. |
| `Induction.EmptyProductUnit` | `273c225f-7fb3-4cf4-852c-88d7816b0bae` / `8364e73f-14ec-4d14-8f2b-1555a7c1ce95` | Actual full-subgroup evaluation and empty tensor unit; no special-head conclusion. Reviewer 8857, commit `e530d1eb7e66b0d2b988684aaaa90a729bda10e2`, integration `351b5bc54d374bde88313e8e0d414501`. |

`ProductVanishing` also has a grouped origin: its Lean matches independently
accepted artifact `6ded142e-bf04-4d18-8956-a5850e80410b`, Reviewer 5828,
commit `7114a39081ee7c0f5e7ab6294392905004234dd3`, integration
`37132ca35c114f708f87ffb4e941dfde`. The current Markdown attribution amendment
is independently published artifact `e85cf101-daae-4eb8-bac1-2f3ee0d0ee3b`,
commit `5e4a58e8c8d5cb559e3acb76c4fab01382a95b91`.
The used `subsingleton_binary` has only the zero-factor premise. No conditional
level theorem in a neighboring bundled module is substituted for an actual
proof of product vanishing.

A comment-stripped scan of the entire closure finds the excluded or later
proposition names only in `Classification.SegmentSocleDerivativesStatement`
and `Classification.MultisegmentClassificationStatement`. These are `Prop`
definitions (including a conjunction of statement definitions), rather than
proofs or supplied hypotheses. In particular the support-shift theorem (c),
its proof module, the special-head criterion, and its derivative proof modules
are absent. The required single-segment proof's permitted BZ77 4.7(b) input
continues to use only the generic quotient-support definition just listed.

| Exclusion, including its proof successors and mathematical consequences | Audit result |
| --- | --- |
| `UnlinkedSegmentSocleProductIrreducible`, task `23e98d90-6055-4e35-91a9-b0f5d8a84961` | No conclusion or proof dependency. |
| `LinkedSegmentSocleReverseProductStructure`, task `a55c4267-7e3a-43f6-8bb1-ce319e1d0aa9` | No conclusion or proof dependency. |
| `LinkedSegmentSoclePairReducible`, task `8fa9f68b-fa1b-431a-97f6-5b163964d1fc` | No conclusion or proof dependency. |
| `JuxtaposedSegmentSocleReverseProductStructure` and `LinkedSegmentSocleReverseProductQuotientHom`, task `7ff2a1e9-89dc-439e-a861-a567b3db92bf` and all proof successors | No conclusion or proof dependency. |
| `SegmentSocleProductIrreducibility`, task `2ae5cbe5-0701-4509-88a0-db8cbeb35be4` | No conclusion or proof dependency. |
| `AdjacentUnlinkedSegmentSocleSwap`, tasks `e3634665-571b-4852-9f4c-bab8a1053434` and `cded83f3-df9c-4018-bc61-dc54f5c1f9ab` | No conclusion or proof dependency. |
| `TwoSegmentSocleCommutation`, tasks `426911b4-6620-413f-8065-04b25287f3bd` and `66e3b87c-647e-41e4-af18-df4d436765f0` | No conclusion or proof dependency. |
| `LinkedSegmentSocleGluing`, tasks `c84cd52c-3ff3-4024-be50-8b84dd480888` and `6780b79c-9526-46aa-b8b4-00377d68b1ea` | No conclusion or proof dependency. |
| `OrderedMultisegmentSocleExistence`, task `23189526-80b0-4828-a6d4-7ebec2cbeef5` | Name occurs only in proposition definitions; no proof is used. |
| Socle exhaustion, task `f3a69bc8-7312-4f82-8a7d-ea3c8188cb63` | Only the explicitly listed generic definitions and tensor/filtration lemmas. |
| Segment analytic classification, task `aca8805b-054f-4d56-8045-12db7f623404` | No conclusion or proof dependency. |
| Special-head multisegment exhaustion, task `3bfb61fa-1129-4fc9-83fd-7fcfec22106e` | No conclusion or proof dependency. |
| Ordered special-head existence, task `ebea9a8a-9b21-4208-aa31-98c2dea1f8a3` | Only the generic data/reduction module in the fixed statement chain. |
| Quotient coverage, task `20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584` | Only generic trivial-group quotient algebra in the fixed statement chain. |
| Ordered conversion, task `8252833d-c269-41a9-824c-5879e531b23b` | Only supplied-data permutation transport in the fixed statement chain. |
| Tempered block uniqueness, task `52e97845-36bb-457d-b76f-70753334b88c` | No conclusion or proof dependency. |
| `GenericSegmentProductUniqueness`, task `30341ae4-65f2-4a0e-9283-763db01a409e` | No conclusion or proof dependency. |
| `SquareIntegrableLanglandsClassification`, task `1cb45da2-7007-4351-a694-594fb148b8d1` | Name occurs only in proposition definitions; no proof is used. |
| Square-integrable exhaustion, task `cd8ab97c-0b78-4bce-97c4-d307a28159a4` | No conclusion or proof dependency. |
| Regular exhaustion, task `bf433f0a-921a-428c-b0c0-6475438125ac` | No conclusion or proof dependency. |
| Forward special-segment essential square-integrability, task `5eece9e8-7f6b-4ea9-abea-a1f9f1b8c807` | No conclusion or proof dependency. |
| `SegmentHeadProductIrreducibility`, task `8364e73f-14ec-4d14-8f2b-1555a7c1ce95`, and its conclusions | Only the generic `SingletonIso` and `EmptyProductUnit` constructions just audited; the criterion and its conclusions are absent. |
| Later support-shift theorem (c), `HighestDerivativeSupportShift`, and later nonjuxtaposed constituent/strict-mono units (d),(e) | No theorem dependency; only the statement-module proposition definitions are present. |

This audit checks mathematical dependencies. An artifact's publication under an
excluded task is not used as permission to import that task's conclusion, and a
statement definition or publication citation is not used as a proof.

## Validation scope

The complete final Lean source has SHA256
`d18191a27a92cd827bfa562d152f404e788d51838fdc11a53029403f9f64d514`.
Recovery check `744784a8-23a6-4046-b8b7-80838274b724` built the helper modules
and final theorem in approved environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f` with zero errors and warnings.
Declaration inspection reports independent universe parameters `uF`, `uV`
and only `propext`, `Classical.choice`, and `Quot.sound` as axioms.
The theorem's explicit result is the unchanged published proposition; formal
proof admission additionally binds the exact-target check to that proposition.
Compilation and development inspection are distinct from independent semantic
acceptance and Library publication.
