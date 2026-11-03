# Supports of constituents of segment derivatives

Worker 508 supplies this focused internal helper for the proof of Zelevinsky
(1980), Proposition 4.3. It proves support witnesses for actual smooth
representations and actual subquotients. The final constituent-level theorem
and the induction over an ordered product are separate obligations.

## Implemented proof

`support_of_embedding` composes an actual subquotient of a representation with
its supplied embedding in an ordered supercuspidal product. The composition is
an actual subquotient presentation of the same cuspidal product. Together with
irreducibility, the original ordered representatives, rank sum, and multiset
equality, this is exactly `IsSupercuspidalSupport`. Thus
`support_of_product` supplies the full multiset of segment members as a support
to every irreducible constituent of a segment-socle product. It invokes the
published `embedsCuspidal_induced`; it assumes no uniqueness of support and
uses no permutation of the factors.

`segment_embedding` applies the same embedding construction to a singleton
segment-product datum, then uses the published ordered singleton isomorphism
and equality transport of ranks. `support_zero` handles rank zero directly:
the empty cuspidal product is the scalar line, and an irreducible
representation of the trivial group is a quotient of that line. This gives
its empty support without a positive-rank hypothesis.

`nontrivial_of_constituent` unpacks an actual subquotient as a quotient of a
subrepresentation. A zero ambient carrier would make that quotient zero,
contradicting simplicity. The rank-transport lemmas preserve support,
irreducibility and the actual occurrence by equality elimination;
`castRank_eq` identifies the two published equality transports used here.

The internal definition `residualContent` retains the complete multiset when
its Boolean is false. For true it removes the last member, or gives the empty
multiset for a singleton. `segment_support` proves that an irreducible
constituent of the order-`i` derivative chooses one of these Booleans, with
`i = 0` for false and `i = Δ.rank` for true. At order zero the derivative is
the identity, so the embedding gives its support. At positive order, the
published `segmentSocleDerivatives` vanishing clause and nontriviality force
`i = Δ.rank`. If the length is at least two, its segment-socle clause
identifies the actual rank-cast derivative as the shortened segment socle;
the embedding gives the shortened content and equality transport returns it
to the original rank. For a singleton the residual rank is zero, handled by
`support_zero`. All multiplicities are retained.

The independent universe parameters are `uF` for the field and `uV` for
segment bases; carriers lie in `max uF uV`. Every theorem retains the supplied
`T.topology`. `segment_support` takes every supplied unitary additive
character, with no existence assumption. It applies the actual
`generalLinearDerivative` with determinant inverse-half normalization. The
new proof uses only identity at order zero, the previously proved actual
segment derivative formula, and equality transports. It introduces no new
Haar-modulus comparison or normalization rule.

## Sources and published inputs

The mathematical route is derived from Zelevinsky (1980), Theorem 3.5
(printed p.182), the support convention §1.10 (p.174), and the proof of
Proposition 4.3 in §4.5 (p.185). The registered original is
`zelevinsky-1980-induced-ii`, SHA256
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
The retained original was read at the printed labels; the corresponding
zero-based PDF indices are 18, 10 and 21. No applicable registered erratum was
found in the supplied literature index or public source notes. This is an
internal packaging of support witnesses, not a new source definition.

The actual segment formula is independently published proof
`ac220f41-e7d4-4c9f-951f-0ff12e51412f`, task
`209027ca-f49c-472a-af2a-f2fc0006950e`, at Library commit
`e530d1eb7e66b0d2b988684aaaa90a729bda10e2`. The embedding infrastructure is
published artifact `5440c02b-fc2d-4abe-bbe8-6cd061c6a683`, commit
`5e4a58e8c8d5cb559e3acb76c4fab01382a95b91`. The ordered datum and singleton
assembly is published artifact `7eb3979e-27f3-4acc-b2e1-b14899167792`, commit
`7543113c99690e18b45f3b22d252e8cf77c3964e`. Their independently reviewed
mathematics is imported by Lean name. A source citation or proposition
definition is not used as a proof.

## Direct and transitive independence

The direct imports are `Classification.SegmentSocleDerivativesProof`,
`Classification.SegmentProductOrderedAssembly`, and
`Classification.SegmentProductCuspidalEmbedding`. A fresh recursive traversal
at Library base `4103487976e26033768519d7c8e53adf6d10c898` finds 1,196 project
modules including this helper. All 1,195 imported Lean files are byte-identical
to that Library base. Every project import resolves and has nonempty paired
Markdown.
The single-segment proof contributes its previously audited 1,178-module
closure. The additional 17 imported modules provide multiset enumeration,
segment members and content, ordered head/tail induction and scalar units,
three-block regrouping and carrier transports, and finite length of supplied
irreducible products. None proves a segment-product classification result.
The finite-length proof is independently published artifact
`41a8585c-a5c2-4d05-a095-e31d28518609`, commit
`ddf3850e87ef10e9eabe230b50f772e4890d71bd`.

The inherited proof's audit distinguishes generic infrastructure published
under excluded hosts from their excluded mathematical conclusions, as
explained by operator responses `2b34e4035a5b5dafad7ad84d5a8c0dd8` and
`10df3136f50c5901b1061d52c6b92e07`. The following such modules are present
in this closure. Their contents, rather than their publishing host, establish
the distinction; no excluded conclusion or dependent proof is used.

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
| `Induction.EmptyProductUnit` | `273c225f-7fb3-4cf4-852c-88d7816b0bae` / `8364e73f-14ec-4d14-8f2b-1555a7c1ce95` | Actual full-subgroup evaluation and empty tensor unit; no special-head conclusion. Reviewer 8857, commit `e530d1eb7e66b0d2b988684aaaa90a729bda10e2`, integration `351b5bc54d374bde88313e8e0d414501`. |

The imported `SegmentSocleDerivativesProof` documents its allowed BZ77 4.7(b)
input and normalization comparison. The generic modules above add no
assumption to its theorem. A comment-stripped scan finds the excluded names
only in the fixed target's imported `MultisegmentClassificationStatement`,
where they are proposition definitions and conjunctions of definitions. No
excluded theorem is supplied as a premise. The audit against every contract
exclusion, including proof successors and transitive conclusions, is:

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


These checks establish the dependency boundary of this helper only. They do
not prove the host task's support containment, product selector induction or
exact constituent-level theorem.
