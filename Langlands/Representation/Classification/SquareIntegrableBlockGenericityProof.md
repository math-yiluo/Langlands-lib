# Genericity of square-integrable block products

Author: Worker 90.

`Langlands.Classification.squareIntegrableBlockGenericity` proves exactly
`Langlands.Classification.SquareIntegrableBlockGenericity.{uF,uV} F T`
from `TemperedBlockStatement`. Its outer parameters are
`{p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)`.
There are no additional hypotheses. The field and representation universes
remain independent, with all block carriers in `Type (max uF uV)`.
The target statement and its imported pairs are unchanged.

The conclusion is full `Whittaker.IsGeneric` for the actual normalized product
of the supplied ordered blocks and every `UnitaryAdditiveCharacter`. It includes
irreducibility, admissibility and a nonzero standard Whittaker functional.
The character retains continuity and nontriviality. The rank is `n + 1`,
including rank one. Induction retains the upper block parabolic, right
translation and positive half-modulus covariance; the Whittaker character
is the given character of the sum of superdiagonal entries.

## Implemented proof

For each original block `σ i`, analytic square-integrability implies essential
square-integrability by the existing zero-twist lemma. Apply the published
`segmentEssentialSquareIntegrableClassification` theorem to its irreducibility
and the positive rank `B.positive i`. This supplies a segment `Δ i`, an equality
`hΔ i : (Δ i).degree = B.size i`, and a strong special-head relation for the
same block transported by `(hΔ i).symm`. The head is the irreducible quotient
of the increasing segment product, with the strong kernel-uniqueness condition.
No new representative of the block is selected.

Build `SegmentProductDatum d` with length `B.length`, segment family `Δ`,
the original degree sum transported pointwise by `hΔ`, and these transported
original blocks. Its `HasSegmentHeads` property is precisely the family
supplied by classification. The private lemma `squareIntegrable_rank_transport`
eliminates a rank equality to transport the original analytic
square-integrability predicate to each `d.blocks i`.

To prove `d.multisegment.IsUnlinked`, express each multiset membership as an
index in its `List.ofFn`. Apply the published
`squareIntegrableSegmentNonlinkage` theorem to the two corresponding supplied
heads and their analytic square-integrability. This handles every pair,
including equal indices and repeated segments, without removing multiplicities.

The private lemma `segmentShape_induced_eq` identifies `d.induced` with
`(T.normalizedProductInductionFunctor B).obj σ`. Destruct `B`, reduce its
projections, and use function extensionality on `hΔ` to identify its size
function with the segment-degree function. Eliminate that equality; proof
irrelevance identifies the positivity and sum proofs and the remaining rank
transports. The equality of the induced objects is then reflexive. This
preserves the entire ordered family and its actual actions.

Finally apply the reverse implication of the published
`genericSegmentProductExhaustion` theorem to the original induced object,
using `d`, its heads, its nonlinkage, and `eqToIso` of the preceding equality
in the required direction. That implication supplies all three parts of
`Whittaker.IsGeneric` for the arbitrary character introduced by the target.

The original invariant-positive-form hypothesis is retained in the exact
statement; this proof does not need it beyond analytic square-integrability.
It does not derive an invariant form from a unitary central character.
Neither the pending square-integrable block-induction theorem nor
`TemperedUnitarityAndGenericity` is used. The finite heartbeat limits only
allow Lean to elaborate the dependent normalized-product expressions.

## Provenance

This is an internal assembly of the three published Lean theorems named
above, imported from `SegmentEssentialSquareIntegrableClassificationProof`,
`SquareIntegrableSegmentNonlinkageProof`, and
`GenericSegmentProductExhaustionProof`. Their paired Markdown explains their
analytic, scalar-action, and top-derivative proofs. This module adds the
rank/shape equality adapters and assembles their conclusions for the target.

Kudla, *The local Langlands correspondence: the non-archimedean case* (1994),
printed p.373 following Proposition 2.2.1, explains the nonlinkage of segments
with square-integrable heads. Section 2.3, printed p.374, gives the standard
Whittaker character, independence of its choice, and the unlinked-segment
criterion in Theorem 2.3.1. These passages describe the route implemented
here; no tempered genericity assertion is assumed as an input.
Registered source: `kudla-1994-local-langlands-nonarchimedean`, SHA-256
`0e1f9bc9986fc136081f0eed1aaafb50302acacb5a23e9538581f2f5b533198b`.

Zelevinsky, *Induced representations of reductive p-adic groups II* (1980),
§9.1, printed p.197, fixes the special quotient convention; §9.3, printed
p.198, states the essential square-integrable classification, with the
converse proof omitted there. The imported classification theorem supplies
an actual Lean proof by its documented independent analytic route.
Theorem 9.7(a), printed p.199, states the genericity and irreducibility of
unlinked products. We use the proved reverse generic-exhaustion implication,
which includes the actual Whittaker-functional comparison, rather than
identifying the source's derivative terminology by definition.
Registered source: `zelevinsky-1980-induced-ii`, SHA-256
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
These original passages were read directly in their retained editions and
the fingerprints verified. No source-specific errata file for either source
is present in the current Library. The source boundaries in
[the classification source note](../../../notes/henniart/gln-classification-sources.md)
remain in force; citations alone supply no theorem.
