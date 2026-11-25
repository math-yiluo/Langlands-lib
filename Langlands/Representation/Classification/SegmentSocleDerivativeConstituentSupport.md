# Supports of constituents of segment derivatives

This module is a focused internal helper for the proof of Zelevinsky
(1980), Proposition 4.3. It proves support witnesses for actual smooth
representations and actual subquotients. The final constituent-level theorem
and the induction over an ordered product are in other modules
(`NonjuxtaposedSegmentSocleConstituentLevelProof` and
`SegmentProductDerivativeConstituentSupport`).

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

The actual segment formula is the published proof
`Classification.SegmentSocleDerivativesProof`, at Library commit
`e530d1eb7e66b0d2b988684aaaa90a729bda10e2`. The embedding infrastructure
(`Classification.SegmentProductCuspidalEmbedding`) is published at commit
`5e4a58e8c8d5cb559e3acb76c4fab01382a95b91`. The ordered datum and singleton
assembly (`Classification.SegmentProductOrderedAssembly`) is published at commit
`7543113c99690e18b45f3b22d252e8cf77c3964e`. Their
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
The finite-length proof `Classification.IrreducibleProductFiniteLengthProof`
is published at Library commit
`ddf3850e87ef10e9eabe230b50f772e4890d71bd`.

The inherited proof's audit distinguishes generic infrastructure published
with excluded developments from their excluded mathematical conclusions.
The following such modules are present
in this closure. Their contents, rather than the development they were published
with, establish the distinction; no excluded conclusion or dependent proof is used.

| Module (relative to `Langlands.Representation`, except `Combinatorics`) | Actual scope |
| --- | --- |
| `Classification.TrivialGroupQuotient` | Quotient algebra for trivial groups, in the fixed statement chain. |
| `Classification.SegmentProductPermutation` | Permutation transport for supplied product data, in the statement chain. The final induction preserves the original order. |
| `Classification.OrderedMultisegmentHeadReduction` | Supplied-data reduction and definitions, in the statement chain; no special-head existence theorem. |
| `Classification.SegmentSocleProductData` | Segment-product data, in the statement chain. |
| `Classification.SingletonSegmentSocle` | The one-segment socle comparison, in the statement chain. |
| `Combinatorics.RelationInversions` | Finite list-inversion counting used by earlier independent inputs. |
| `Filtration.ObjectTransport` | Pullback and inverse-image transport of supplied actual filtrations. |
| `Classification.CuspidalProductDerivativeQuotientSupport` | Quotient form of BZ77 4.7(a), used inside the BZ77 4.7(b) proof; no later support-shift theorem. |
| `Induction.EmptyProductUnit` | Actual full-subgroup evaluation and empty tensor unit; no special-head conclusion. Published at commit `e530d1eb7e66b0d2b988684aaaa90a729bda10e2`. |

The imported `SegmentSocleDerivativesProof` documents its BZ77 4.7(b)
input and normalization comparison. The generic modules above add no
assumption to its theorem. A comment-stripped scan finds the excluded names
only in the fixed target's imported `MultisegmentClassificationStatement`,
where they are proposition definitions and conjunctions of definitions. No
excluded theorem is supplied as a premise. The audit against every
exclusion, including proofs and transitive conclusions, is:

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


These checks establish the dependency boundary of this helper only. They do
not prove the support containment, product selector induction or
exact constituent-level theorem of Proposition 4.3.
