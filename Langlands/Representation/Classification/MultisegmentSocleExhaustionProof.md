# Independent Zelevinsky multisegment socle exhaustion

Author: Worker 494.

This module proves the unchanged proposition
`Langlands.Classification.MultisegmentSocleExhaustion.{uF,uV} F T` from
`Langlands.Representation.Classification.MultisegmentClassificationStatement`.
The theorem is `Langlands.Classification.multisegmentSocleExhaustion`, with
exactly the outer parameters `{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)`
and `(T : F.TopologicalData)`. The field and carrier parameters remain
independent. There is no additional theorem-valued assumption.

For every natural rank `n` and actual irreducible
`π : SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear n F.Carrier)`, the theorem
produces `a : T.Multisegment.{max uF uV,uF}`, proves `a.degree = n`, and
proves `a.IsZelevinskySocle π`. This last relation exhibits actual product
data at rank `n`, with the required nonprecedence order, actual individual
segment socles, an injective intertwiner from `π` into the full normalized
upper-parabolic product, and uniqueness of its irreducible subobject as an
image. The topology throughout is the supplied `T.topology`.

## Implemented argument

The proof constructs the two fields of
`HasIndexedSocleEmbeddingReductions` for the given actual `π`.
For an adjacent unlinked pair, the published
`adjacentUnlinkedSegmentSocleSwap` supplies an isomorphism of the two full
actual products. `SmoothRep.equivOfIso` and
`IsIrreducibleSubrepresentation.of_equiv` transport the actual embedding,
while `HasSegmentSocles.permute` retains all individual socle certificates.
For an adjacent preceding pair, the published
`linkedSegmentSocleEmbeddingReduction` supplies either the swapped actual
embedding or replacement data at the same rank. The replacement retains the
exact prefix and suffix occurrences and inserts the union segment and the
optional intersection segment. Its support equalities, exact list identity,
individual socle certificates and actual embedding are exactly the second
indexed rule. Repetitions are retained.

Next `HasIndexedSocleEmbeddingReductions.exists_ordered` is applied with the
proved `cuspidalIntegralTwistFreeness` and the nonempty collection supplied by
`T.exists_segmentSocleEmbedding π hπ`. The latter starts at positive rank
from `glSupercuspidalEmbedding`, replaces each actual cuspidal block by its
singleton segment socle, and transports the injective intertwiner through
the actual product equivalence. At rank zero it starts from precisely
`SegmentProductDatum.empty` and the elementary empty-product embedding.

The indexed minimization adapter retains the fixed rank, actual blocks and
embedding while translating to the predicate `SocleEmbeddingList π` on lists.
`HasLocalSegmentReductions.exists_ordered` minimizes the natural-number
precedence inversion count using `Nat.find`; finiteness of the collection of
representation data is unnecessary. If the count is positive, unrelated
swaps expose an adjacent preceding pair without changing the count. Twist
freeness rules out precedence cycles and reverse precedence. The linked rule
then gives either a related swap or a union/intersection replacement, each
with strictly fewer inversions. This contradiction gives genuine
nonprecedence-ordered actual data `d` with `d.HasSocleEmbedding π`.

The published `orderedMultisegmentSocleExistence` now gives a strong
irreducible socle of this same full product. The elementary
`HasSocleEmbedding.isZelevinskySocle_of_exists` transfers that property to the
already embedded `π`: uniqueness of irreducible images in the product equates
each such image with the image of the given embedding. Thus the proof obtains
the strong socle relation, rather than only occurrence as a constituent.
Finally it returns `d.multisegment`, the exact equality
`d.multisegment_degree`, and the datum `d` itself as witness. The entire
argument includes rank zero and introduces no positivity assumption.

## Published inputs and provenance

All mathematical inputs are imported by their current Library Lean names.
The direct representation-theoretic proof modules are
`AdjacentUnlinkedSegmentSocleSwapProof`,
`LinkedSegmentSocleEmbeddingReductionProof`,
`OrderedMultisegmentSocleExistenceProof`,
`SegmentSocleEmbeddingExistence`, and `CuspidalIntegralTwistFreenessProof`.
The last embedding module and the conditional combinatorial and actual-data
adapters were separately published as supporting constructions for this task.
Every conditional premise used by those adapters is discharged here by a
proved theorem.

In particular, the exact linked reduction was independently approved by
Reviewer 11702 under review `b5c282b5-fcc4-4f72-8fc2-3c5900ff455e` and
published as artifact `668c8c0c-020f-4fac-b8ce-0df8f954a145` at Library
commit `1fddae33727cfcfcc52ed326c69373200a28ff87`. Its original validator
`80dbd988-6f88-44cf-a251-d80fa41b10c4` passed Lake build, exact-target,
unchanged-statement and frozen-input checks. The adjacent-swap theorem was
independently approved under `7764f636-00f0-49e0-bf03-e76a7f7b1696` and
published as `1e21b958-60f9-48ee-85b5-e8c69928e016`. Ordered strong-socle
existence was independently approved under
`3fc37caf-af93-467a-8264-a0ba10b03378` and published as
`987cfe05-0662-4431-a4fa-40156b59a263`. Their complete unapplied types have
only the stated prime, field and topology arguments, with independent universe
parameters. These receipts establish the input publication boundary; they
are not mathematical hypotheses of this theorem.

The implemented proof is the direct socle argument of Zelevinsky,
*Induced representations of reductive p-adic groups II* (1980), Theorem
6.1(c), printed p.188/PDF25, §6.5, p.189/PDF26, and §6.7, p.190/PDF27.
Registered literature ID: `zelevinsky-1980-induced-ii`; retained PDF SHA256:
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
The source's finite-set minimum is implemented by a minimum of attained
natural-number inversion counts. Its local forward two-layer argument uses
the independently proved gluing theorem: Proposition 4.6 concerns the reverse
pair, and independent two-factor constituent commutativity supplies the
forward filtration. No forward exact-sequence orientation is inferred from
Proposition 4.6 alone. This module only composes the already proved local
and ordered-socle inputs with the actual-data minimization machinery.

## Independence audit

The excluded mathematical conclusions are segment analytic classification
(`SegmentEssentialSquareIntegrableClassification`), special-head multisegment
exhaustion (`MultisegmentHeadExhaustion`), ordered special-head existence
(`OrderedMultisegmentHeadExistence`), quotient coverage
(`OrderedMultisegmentQuotientExhaustion`), `TemperedBlockUniqueness`,
`SquareIntegrableLanglandsClassification`,
`SquareIntegrableLanglandsExhaustion`, and
`GLRegularLanglandsExhaustionStatement`. The exclusion includes proof
successors and their transitive proof dependencies.

Each substantive input was checked through its implemented proof and its
transitive declarations before use. The initial cuspidal embedding uses
Jacquet-module maximality, Frobenius reciprocity, admissibility, tensor
factorization and universe realization. The singleton and empty-rank bridges
use actual one-block and scalar-line equivalences. Twist freeness uses the
central-character/determinant argument. The combinatorial steps use actual
segment support coordinates, occurrence counts and natural-number minima.
None derives its input from an excluded classification conclusion.

The adjacent-swap proof uses independently proved two-segment socle commutation
and actual ordered regrouping. The linked reduction uses the independent
forward two-factor gluing proof and actual filtration, induction, regrouping
and slot-replacement maps. The gluing proof uses reverse-pair structure,
independent two-factor constituent commutativity and Jordan–Hölder comparison.
The ordered-socle proof uses actual highest derivatives, truncation order,
independently proved homogeneity, mirabolic strong indecomposability and
Artinian extraction. Its general detection input is proved on the BZ77 route;
the independently proved Ze80 single-segment formula enters the consumer,
without entering that detection theorem.

The complete linked-reduction import inventory contains 1,386 project modules;
every inherited Lean/Markdown pair matches the public Library at
`1fddae33727cfcfcc52ed326c69373200a28ff87`. Its declaration traversal follows
types, values including private and opaque constants, and inductive
constructors, reaching 95,442 constants, including 16,397 project constants
in 1,146 defining project modules. It reaches no excluded conclusion.
Corresponding complete audits were retained for the adjacent and ordered
inputs and their lower proof branches.

Some imported files define excluded propositions or conditional head
assemblies without proving them. Such imports do not supply their conclusions.
The permitted shared helper
`RegularHeadExistence.nontrivial_normalizedProductInduction` constructs a
nonzero tensor and compact local section; it does not prove a regular-head
classification or exhaustion statement. The empty-rank bridge likewise uses
only elementary scalar-line and empty-product facts from shared modules.
These distinctions were checked at declaration level as well as by reading
the actual proof routes. The full socle irreducibility criterion and all
special-head classification proofs are unnecessary here.

The final theorem's own complete declaration audit reaches 96,573 constants,
including 17,386 project constants in 1,203 defining project modules. The only
exhaustion or other exclusion-pattern matches are this theorem and its own
target proposition. Its full source import inventory has 1,436 project modules,
with no missing import or excluded proof module; every inherited Lean/Markdown
pair is byte-identical to the public Library at the commit above. Every reached
defining project module lies in that inventory. The diagnostic also assigns
the complete unapplied theorem to the required independent-universe telescope.
The declaration audit supplements the substantive proof-route checks above;
a name scan alone does not establish mathematical independence.

The theorem is checked in approved environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`. Its only axioms are `propext`,
`Classical.choice` and `Quot.sound`. No target statement or imported pair is
modified by this contribution. Development compilation does not replace
independent semantic review, exact-target validation or publication.
