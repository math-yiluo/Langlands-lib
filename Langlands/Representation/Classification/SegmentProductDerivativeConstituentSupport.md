# Support selectors for ordered-product derivative constituents

This module supplies an internal construction used in the proof of Zelevinsky
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

| Published module, relative to `Langlands.Representation` | Publication commit |
| --- | --- |
| `Classification.SegmentSocleDerivativeConstituentSupport` | `9d1720cbedcfd184cf48bf36249fc3029583cafa` |
| `Derivative.ProductDerivativeSupportAggregation` | `1271a6b7c9a470deaa1b8e2aadc2e2defd10f5b5` |
| `Derivative.GeneralLinearDerivativeFiniteLengthProof` | `47b67c4eb87954cf163f3a88bb94b9cbae2edbf0` |

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
published with the excluded developments remain generic; their provenance and
scope are listed in the paired single-segment helper. These lower constructions
are distinct from the excluded mathematical conclusions. The order in this construction
is the original order throughout.

The full dependency boundary, including proofs and transitive
mathematical conclusions, is preserved:

| Exclusion, including its proofs and mathematical consequences | Audit result |
| --- | --- |
| `UnlinkedSegmentSocleProductIrreducible` | No conclusion or proof dependency. |
| `LinkedSegmentSocleReverseProductStructure` | No conclusion or proof dependency. |
| `LinkedSegmentSoclePairReducible` | No conclusion or proof dependency. |
| `JuxtaposedSegmentSocleReverseProductStructure` and `LinkedSegmentSocleReverseProductQuotientHom`, and all their proofs | No conclusion or proof dependency. |
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
| `SegmentHeadProductIrreducibility` and its conclusions | Only the generic constructions just audited; the criterion and its conclusions are absent. |
| The support-shift theorem `HighestDerivativeSupportShift` and the nonjuxtaposed results `NonjuxtaposedSegmentSocleConstituentLevel` and `NonjuxtaposedSegmentSocleDerivativeStrictMono` | No theorem dependency; only the statement-module proposition definitions are present. |


The final row records the stronger boundary of this focused helper: the
support-shift theorem is not needed here. The proof
`Classification.NonjuxtaposedSegmentSocleConstituentLevelProof` combines this
construction with that theorem and the nonjuxtaposition combinatorics.
