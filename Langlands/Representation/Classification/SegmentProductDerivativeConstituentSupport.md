# Support selectors for ordered-product derivative constituents

Worker 508 supplies an internal construction used in the proof of Zelevinsky
(1980), Proposition 4.3. It applies to every ordered segment-product datum and
every irreducible actual subquotient of a bounded derivative of its induced
representation. It retains repeated segments and the original positions.
No nonjuxtaposition hypothesis is needed for this support construction.

## Construction and implemented proof

`supportSelector` returns a Boolean at each original position, together with
proofs that the derivative order is the sum of the selected segment ranks
and that the sum of the corresponding residual multisets is an actual
supercuspidal support of the supplied constituent. Its existence proof is
`product_support`. The residual multiset is the published
`SegmentSocleDerivativeConstituentSupport.residualContent`: false retains
all segment members, and true removes the last member, giving the empty
multiset for a singleton. All multiset multiplicities are retained.

For positive ambient rank, the proof specializes the independently published
`ProductDerivativeSupport.supportData`. The allowed property for a factor
says that its derivative order and support are respectively the zero/rank
choice and the residual multiset for one Boolean. The factor derivative has
finite length by `generalLinearDerivativeFiniteLength`, since each supplied
segment-socle block is irreducible. The independently published
`segment_support` supplies the allowed support for every actual simple
factor constituent. The generic ordered-product construction then provides
factor witnesses at their original labels, their order sum and the actual
support sum. Choosing the Booleans from those witnesses gives the result.
The proof rewrites an equality of whole finite sums; it introduces no
permutation or distinctness assumption on the segment labels.

At ambient rank zero, positive block sizes force the original position type
to be empty, and the derivative order is zero. The published `support_zero`
provides the empty support directly. This includes the empty ordered product.
The wrapper `supportSelector` chooses the witnessed Boolean function, keeping
the order equality and support proof as subtype evidence.

The independent parameters are `uF` for the field and `uV` for segment
bases; representation carriers lie in `max uF uV`. All supplied topologies
are exactly `T.topology`. The construction takes every supplied unitary
additive character, without an additive-character existence premise. It
uses the actual `generalLinearDerivative` and its determinant inverse-half
normalization. Normalization and exactness enter through the published
segment and ordered-product results; no new Haar comparison is asserted.
This helper does not assert the final constituent-level theorem.

## Provenance and published inputs

This is derived packaging of the support-selection step in Zelevinsky,
*Induced representations of reductive p-adic groups II* (1980), Proposition
4.3, proof §4.5, printed p.185, together with the segment formula, Theorem
3.5, p.182. The registered original is `zelevinsky-1980-induced-ii`, SHA256
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
The actual product-filtration route is Bernstein–Zelevinsky (1977), Lemma
4.5 and §4.6, printed p.455, registered as
`bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
The retained original pages were read at PDF indices 18 and 21 for Ze80
and 15 for BZ77. No applicable registered erratum was found in the supplied
literature index or public source notes. These citations explain the
mathematical route; the construction below uses published Lean proofs.

| Published module, relative to `Langlands.Representation` | Independently accepted artifact | Publication commit |
| --- | --- | --- |
| `Classification.SegmentSocleDerivativeConstituentSupport` | `5671cd1a-0f31-40db-b0f2-edada9b0960a` | `9d1720cbedcfd184cf48bf36249fc3029583cafa` |
| `Derivative.ProductDerivativeSupportAggregation` | `88bf6476-51bf-4016-83db-68b65ba83479` | `1271a6b7c9a470deaa1b8e2aadc2e2defd10f5b5` |
| `Derivative.GeneralLinearDerivativeFiniteLengthProof` | `fa9c4bdb-4d9c-4ca6-9eb0-dddded5e242f` | `47b67c4eb87954cf163f3a88bb94b9cbae2edbf0` |

These are imported by Lean name. The finite-length proof uses exactness,
supercuspidal embeddings, finite length for cuspidal-product derivatives and
induction on representation length. The generic ordered support construction
uses actual Leibniz graded constituents and binary support aggregation.
Its proof and its upstream filtration/exactness proofs have no segment
classification premise. The single-segment helper invokes the published
segment formula and actual cuspidal embeddings, with the dependency boundary
explained in its paired Markdown.

## Direct and transitive independence

The three direct imports are exactly the modules in the preceding table.
A recursive traversal at Library base
`9d1720cbedcfd184cf48bf36249fc3029583cafa` finds 1,269 project modules,
including this new module, and 323 directly named external import roots.
Every project import resolves and has nonempty paired Markdown. All 1,268
imported Lean sources are byte-identical to the Library base. The new
construction adds no theorem-valued premise to these published inputs.

The comment-stripped identifier scan finds the excluded names only as
proposition definitions in `SegmentSocleDerivativesStatement` and
`MultisegmentClassificationStatement`, or conjunctions of those definitions.
No such proposition is discharged or passed as a premise. The inspected
single-segment and generic ordered support proofs establish the mathematical
dependency boundary, rather than relying on this scan alone. In particular,
generic data, tensor units, permutation transport and filtration algebra
published under excluded host tasks remain generic; their provenance and
scope are listed in the paired single-segment helper. The operator's
responses `2b34e4035a5b5dafad7ad84d5a8c0dd8` and
`10df3136f50c5901b1061d52c6b92e07` distinguish these lower constructions
from excluded mathematical conclusions. The order in this construction
is the original order throughout.

The full contract boundary, including proof successors and transitive
mathematical conclusions, is preserved:

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
| Later support-shift theorem (c), `HighestDerivativeSupportShift`, and later nonjuxtaposed constituent/strict-mono units (d),(e) | No theorem dependency; only the statement-module proposition definitions are present. |


The final row records the stronger boundary of this focused helper: the
permitted later support-shift theorem (c) is not needed here. The host proof
will separately combine this construction with that theorem and the
nonjuxtaposition combinatorics. Compilation and staging do not establish
independent mathematical acceptance or the host task's completion.
