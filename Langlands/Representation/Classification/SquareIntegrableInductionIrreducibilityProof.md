# Irreducibility of normalized induction of square-integrable blocks

Author: Worker 452. The ordered rank adapter follows the existing
`TemperedBlockUniquenessReduction` construction by Worker 346 and the
corresponding adapter discussion with Worker 90.

The theorem `Langlands.Classification.squareIntegrableBlockInductionIrreducibility`
proves the unchanged published proposition
`Langlands.Classification.SquareIntegrableBlockInductionIrreducibility.{uF,uV} F T`.
Its only outer parameters are the arbitrary prime, p-adic field, and supplied
topological data. It adds no premise. The original ordered block family,
analytic square-integrability, unitarizability, independent universes, actual
smooth complex representations, upper normalized induction, positive half
modulus, and right translation are retained.

The proof uses the published analytic strong-head segment classification on
each original block. Square-integrability implies essential
square-integrability by the zero real twist. Choose its segment and degree
equality, and retain the same representation transported along that equality.
The private `segmentDatum` records these blocks in the original order.

The private rank-transport lemma preserves square-integrability by eliminating
equality of natural ranks. Apply `squareIntegrableSegmentNonlinkage` to every
pair of the resulting actual heads. Each member of the datum's multisegment
comes from an original occurrence index, so this proves the full nonlinkage
predicate, including repeated segments.

At positive ambient rank, the sufficient implication of
`segmentHeadProductIrreducibility` proves irreducibility of the datum's actual
induction. The criterion is instantiated with segment universe `max uF uV`;
idempotence of `max` leaves every representation carrier in the target
universe. The private `segmentDatum_induced_iso` destructs the original block
shape, identifies the segment-degree function with its size function, and
eliminates that equality. The two induced objects then agree by reflexivity
and proof irrelevance. Transport along this actual isomorphism gives the exact
target conclusion. No block permutation, parabolic reversal or change of
representation model occurs.

This is an internal assembly of three proved Library results:

| Theorem in `Langlands.Classification` | Published proof and use |
| --- | --- |
| `segmentEssentialSquareIntegrableClassification` | [Analytic segment classification](SegmentEssentialSquareIntegrableClassificationProof.md): presents each original block as an actual strong special head. |
| `squareIntegrableSegmentNonlinkage` | [Nonlinkage](SquareIntegrableSegmentNonlinkageProof.md): analytic square-integrability of the supplied heads excludes linkage. |
| `segmentHeadProductIrreducibility` | [Product criterion](SegmentHeadProductIrreducibilityProof.md): its sufficient implication proves irreducibility of the actual ordered product. |

The segment route is the alternative described in the
[target's Markdown](SquareIntegrableInductionIrreducibilityStatement.md).
The three input pairs document their original sources and implemented proofs;
the local helpers here are internal equality transports and a datum constructor.
The final proof does not apply tempered block uniqueness, tempered exhaustion,
the parent block-induction statement as a theorem, or square-integrable
Langlands classification. The rank adapter is reproduced locally so that the
uniqueness reduction is not imported. The unitarizability hypothesis is
retained in the exact target; these stronger analytic segment inputs already
establish the irreducibility conclusion without using that conjunct.

The source audit at Library `b8342b18a9c917d5ef97606f056f47113f610808`
finds 1,580 project modules including this new module, and 353 distinct
external frontier imports. Every inherited Lean/Markdown pair is unchanged
from that Library; every project import is present and every paired Markdown
file is nonempty. Removing nested comments and strings before scanning finds
no proof holes, new axioms or prohibited executable syntax. The recursive
project counts for the four direct imports, including each import itself, are:

| Direct import after `Langlands.Representation.Classification.` | Project modules |
| --- | ---: |
| `SquareIntegrableInductionIrreducibilityStatement` | 65 |
| `SegmentEssentialSquareIntegrableClassificationProof` | 1,575 |
| `SquareIntegrableSegmentNonlinkageProof` | 76 |
| `SegmentHeadProductIrreducibilityProof` | 1,344 |

The inherited `TemperedBlockStatement` and
`MultisegmentClassificationStatement` modules contain proposition definitions
for downstream induction, exhaustion, uniqueness and square-integrable
Langlands classification. Their occurrences are definitions or conjunctions
of those definitions, not assumed or proved inputs. No proof or reduction
module for those downstream conclusions is in this import closure.
The analytic classification and product-criterion pairs explain their lower
Jacquet-word, scalar-cone and general-derivative routes and their independence
audits. The present audit combines those published explanations, inspection
of the direct theorem interfaces and local proof, recursive import and byte
comparison, and name scans; it does not claim to reread all inherited proofs.
General tempered-exponent lemmas in the closure are analytic inputs, not
tempered block exhaustion.

The product criterion's published proof records the operator rulings for its
general derivative route and support-only terminal bound. Those rulings
describe its permitted foundations; they provide no mathematical premise to
this assembly. This proof calls only the final criterion, not its restricted
length-two internal lemmas. The current nonlinkage proof incorporates the
published extraction of `Segment.support_subset_of_base_shift` into
`SegmentSupportContainment` and the shared scalar determinant-norm lemma;
its theorem and conclusion are unchanged.

Full-module development compilation and a Lake build with theorem inspection
succeed with zero errors and warnings in environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`. Inspection reports exactly the
independent levels `uF,uV` and the axioms `propext`, `Classical.choice` and
`Quot.sound`. These are development checks; exact-target candidate validation,
independent semantic review and publication are separate admission steps.
Only this new Lean/Markdown pair is submitted.
