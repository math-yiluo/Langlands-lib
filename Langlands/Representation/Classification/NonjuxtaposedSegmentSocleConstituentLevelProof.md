# Constituent level for nonjuxtaposed segment-socle products

Authors: Worker 508 (proof and explanation), with Worker 593 (support
combinatorics and identification of the published actual-subrepresentation
extraction route).

`Langlands.Classification.nonjuxtaposedSegmentSocleConstituentLevel` proves
exactly the published proposition
`Langlands.Classification.NonjuxtaposedSegmentSocleConstituentLevel.{uF,uV} F T`
from `SegmentSocleDerivativesStatement`. Its only outer parameters are
`{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)`.
It adds no theorem-valued premise and changes none of the target's imports.

For every supplied unitary additive character, ordered segment-product datum
with segment-socle blocks, and free `k ≤ n` equal to the sum of the segment
ranks, the theorem gives each irreducible actual subquotient of the induced
product a nonzero order-`k` derivative and zero derivatives at every higher
bounded order. The separation premise excludes juxtaposition only between
distinct positions. Repeated equal segments and every ordering are retained;
there is no nonlinkage or product-irreducibility premise.

## Implemented proof

Fix an actual irreducible constituent `ω`. Consider the natural numbers
`j ≤ n` for which the actual derivative `ω^(j)` is nontrivial. This set
contains zero: the order-zero derivative is the identity, and irreducibility
makes the original carrier nontrivial. `Nat.findGreatest` chooses its largest
member `m`. Its specification supplies the actual bound and nontriviality
witness. If a higher bounded derivative were nontrivial, the maximality
lemma would give `j ≤ m`, a contradiction. Thus all higher bounded
derivatives are subsingleton. No positive ambient-rank assumption is used.

The published `generalLinearDerivativeFiniteLength` makes `ω^(m)` finite
length because an irreducible representation has finite length. The
published `SmoothRep.renardFiniteLength_iff` converts that exact group-algebra
predicate to the categorical finite-composition-chain predicate. The
published `exists_irreducible_subrepresentation_of_finiteLength` then supplies
an actual irreducible smooth representation `σ` and an injective intertwiner
`j : σ ⟶ ω^(m)`. The carrier universe is preserved. This is an actual
subrepresentation, as required by the support-shift theorem.

The injection gives an actual subquotient occurrence. Exactness of the
published derivative functor maps `ω`'s original subquotient occurrence
through the derivative. `smoothSubquotientTransitivity` composes the two
occurrences, so `σ` is an actual constituent of the order-`m` derivative of
the original ordered product. Applying the published `product_support`
chooses a Boolean `bs i` at every original segment position, and gives

- `m = ∑ i, if bs i then (d.segments i).rank else 0`;
- an actual supercuspidal-support witness for `σ`, equal to the sum of the
  residual contents selected by those Booleans.

False retains the full segment; true removes the final member and gives
empty content for a singleton. All multiset multiplicities are kept.
The independently published `support_of_product` supplies a support of `ω`
equal to the complete multisegment content. This is proved using actual
cuspidal embeddings and subquotient transitivity, without requiring a new
uniqueness or permutation assertion here.

Apply the published `highestDerivativeSupportShift` to `ω`, its highest
order `m`, the actual injection of `σ` and these two support witnesses. Its
conclusion is positive unit-twist containment:

```
(residual content).map (CuspidalDatum.twist 1) ≤ full content.
```

The private helper `residualContent_eq` identifies the support selector's
explicit conditional definition with the published finite-multiset helper's
`lower.map.getD` convention, by cases on the Boolean and on segment length.
`fullContent_eq` expresses the original multisegment content as the finite
sum of its indexed segment contents. Rewriting those equalities gives
exactly the premise of `NonjuxtaposedSegmentSupport.sum_orders_eq_sum_ranks`.
The latter uses the independently proved `cuspidalIntegralTwistFreeness`.
An unshortened segment would force its shifted end to occur as a segment
beginning. Integral twist freeness rules out its own beginning, and an
occurrence at a different position gives juxtaposition, contradicting the
supplied premise. Therefore all selected orders are the segment ranks,
and the sum equality proves `m = k`.

The private `nontrivial_of_order_eq` transports nontriviality along this
order equality by equality elimination, including the dependent bound
proofs. The higher-vanishing clause follows from maximality and `m = k`.
This establishes both clauses at the free order supplied by the target.

## Universes, topology and normalization

The field universe `uF` and segment-base universe `uV` are independent. Every
smooth carrier in the target and the construction is in `max uF uV`.
The finite-length comparisons and extraction keep that exact universe,
without an extra smallness or universe-lift premise. Inspection of the
compiled final theorem reports exactly the parameters `uF` and `uV`.

Every instance is the supplied `T.topology`. The proof quantifies over every
supplied nontrivial unitary additive character and assumes no character
exists. The derivative is the unchanged
`Langlands.Derivative.generalLinearDerivative`, with its determinant
inverse-half normalization. The new proof manipulates those actual functor
objects, exact subquotients and support multisets; it introduces no other
normalization. The segment and Leibniz proofs use the independently proved
`mirabolicRadicalHaarModulus` comparison where needed, in
`Group.GL.MirabolicModulusProof`, proof task
`f947a735-872d-44db-a9ea-954d17dec4bd` for statement task
`a622f240-4846-4086-b34f-f650ba636ee4`. Its independently published artifact
is `f25fdd6c-d842-40be-b220-92bda8715865`. The support-shift proof works
with the actual determinant normalization directly, as its paired Markdown
explains. The positive twist is `ρ ↦ νρ`, with `ν = |det|`; that direction
is essential to the shifted-end/beginning contradiction.

The proof includes rank zero, the empty product and singleton segments.
The support constructor handles the empty block index directly, and the
support-shift theorem includes zero residual rank. No extra edge-case
hypothesis appears in the final theorem. Kernel inspection of the compiled
theorem reports only `propext`, `Classical.choice` and `Quot.sound`.

## Original sources and provenance

The governing original is A. V. Zelevinsky, *Induced representations of
reductive p-adic groups II. On irreducible representations of GL(n)* (1980),
registered as `zelevinsky-1980-induced-ii`, SHA256
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
The target is Proposition 4.3, printed p.184, with proof §4.5, p.185.
The proof uses Theorem 3.5, p.182, and support properties §4.4(a)–(d),
p.185. Those retained original pages were read at zero-based PDF indices
18, 20 and 21. The positive containment agrees with §4.4(d) when its
multiplicity-function convention is read together with its definition
`(νφ)(ρ) = φ(νρ)`.

The inherited actual-filtration and support-shift inputs come from
I. N. Bernstein and A. V. Zelevinsky, *Induced representations of reductive
p-adic groups I* (1977), registered as
`bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`:
§4.3–4.4, printed p.454; Lemma 4.5, Corollary 4.6 and Lemma 4.7(b),
p.455. The original was read at zero-based PDF indices 14 and 15.
No applicable registered erratum was found for either original in the
supplied literature index or public source notes.

The chosen bounded maximum, exact functor/subquotient composition,
finite-length extraction adapters and definitional content comparisons
are internal implementation steps. They formalize the printed §4.5 route
using actual smooth objects. Cited source passages are not treated as Lean
proofs. All mathematical inputs below are imported by Lean name from
independently accepted publications.

## Published proof dependencies

| Module, relative to `Langlands.Representation` | Independently accepted artifact | Publication commit |
| --- | --- | --- |
| `Classification.SegmentProductDerivativeConstituentSupport` | `fe277145-8ec9-4367-874f-295b822b0119` | `223b9c65844ea8eecb00eafaad77269b9b54d787` |
| `Classification.SegmentSocleDerivativeConstituentSupport` | `5671cd1a-0f31-40db-b0f2-edada9b0960a` | `9d1720cbedcfd184cf48bf36249fc3029583cafa` |
| `Classification.NonjuxtaposedSegmentSupport` | `c655159d-bdd5-4aa7-8889-eebddeee01ff` | `5d3754ec863f6d5013aca65cbcec0801e6972d1f` |
| `Classification.CuspidalIntegralTwistFreenessProof` | `a7545313-ab91-4eaf-881e-2ad0d4c58e56` | `f2f4a196a2ec57cae218f1368dade88282ce7207` |
| `Classification.HighestDerivativeSupportShiftProof` | `69a2f4a3-5ed8-49ad-9570-2e54ca7fd84c` | `8415f6175c53876deb57d52d6700854f946e8529` |
| `Category.RenardFinitenessProof` | `cfa3e67c-f4bd-4a63-9c59-a2890a9f753d` | `9d1720cbedcfd184cf48bf36249fc3029583cafa` |
| `Smooth.RenardIrreducibleExistenceProof` | `8f5306ec-f8f5-475d-8a64-6fa123e36a75` | `5d3754ec863f6d5013aca65cbcec0801e6972d1f` |
| `Derivative.GeneralLinearDerivativeFiniteLengthProof` | `fa9c4bdb-4d9c-4ca6-9eb0-dddded5e242f` | `47b67c4eb87954cf163f3a88bb94b9cbae2edbf0` |
| `Derivative.ProductDerivativeSupportAggregation` | `88bf6476-51bf-4016-83db-68b65ba83479` | `1271a6b7c9a470deaa1b8e2aadc2e2defd10f5b5` |

The last two inputs enter through the product selector. Its individual
segment-support proof uses the independently published
`segmentSocleDerivatives`, artifact `ac220f41-e7d4-4c9f-951f-0ff12e51412f`,
commit `e530d1eb7e66b0d2b988684aaaa90a729bda10e2`. Its actual generic
ordered-support constructor uses exact derivative transport and actual
Leibniz graded constituents. `ExactSmoothSubquotients` is the seventh
direct import here and is already part of that generic construction's
audited published closure. No statement definition is substituted for a
proof of an input.

## Direct and transitive independence

The direct imports are the product support selector, nonjuxtaposed support
combinatorics, integral twist freeness, highest-derivative support shift,
the categorical finite-length comparison, actual irreducible extraction,
and exact smooth subquotient transport. The actual derivative, exactness
and Leibniz filtration, finite length, cuspidal embeddings and support
infrastructure are the permitted shared lower inputs.

At Library base `d33f9cecd12cc3314c6ca208896e6d7b79dec546`, a recursive
audit finds 1,297 project modules including this final module and its
independently published product selector, and 337 directly named external
import roots. Every project import resolves and has nonempty paired
Markdown. The other 1,296 Lean/Markdown pairs are byte-identical to that
Library base. The complete 114-module target import closure, including
the target itself, is unchanged in both Lean and Markdown.

Relative to the 1,269-module product-selector closure, the 28 extra modules
consist of this final module, 20 generic categorical finiteness/extraction
modules, the permitted support-shift proof and its four lower comparison,
embedding and boundary modules, and two finite-multiset combinatorial
modules. The generic categorical proofs use composition chains, subobject
order comparisons and simple quotients; they have no segment input. The
finite-multiset helper uses only segment definitions, twist arithmetic
and the independently proved freeness result. The support-shift proof has
its independently reviewed positive-twist, normalization and transitive
independence audit, preserved by exact-byte comparison here.

A comment-stripped scan finds excluded identifiers only as proposition
definitions or their conjunctions in the fixed statement chain. The
permitted support-shift theorem and the new theorem's own name also appear,
as expected. This lexical check is supplemented by the actual proof route
and the published upstream audits; no excluded proposition is assumed as
a theorem or supplied as a premise.

Generic infrastructure published under excluded host tasks is kept distinct
from their excluded mathematical conclusions, as the complete trusted
operator responses `2b34e4035a5b5dafad7ad84d5a8c0dd8` and
`10df3136f50c5901b1061d52c6b92e07` explain. The lower single-segment support
pair lists those generic modules and their exact provenance: trivial-group
quotients, supplied-data permutation/reduction, segment-product data,
singleton comparison, inversion counting, filtration transport and the
empty tensor unit. The actual final construction retains the original
order. None of those modules proves or assumes an excluded full
classification conclusion.

The audit preserves every contract exclusion, its proof successors and
transitive mathematical consequences:

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
| `SegmentHeadProductIrreducibility`, task `8364e73f-14ec-4d14-8f2b-1555a7c1ce95`, and its conclusions | Only the generic constructions just audited; the criterion and its conclusions are absent. |

The permitted highest-derivative support-shift result (c) is used exactly as
stated. The later strict-monotonicity result (e) and the segment-product
irreducibility, commutation, gluing and classification conclusions are
absent from the proof dependencies. This supplies the constituent-level
input for those subsequent arguments without depending on them.
