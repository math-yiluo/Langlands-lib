# Proof of the segment-polynomial comparison

Module `Langlands.Representation.Aubert.SegmentPolynomialComparisonProof`, namespace
`Langlands.Aubert`.

## Result

`segmentPolynomialComparison F T hx hl : SegmentPolynomialComparisonStatement F T hx hl`
for every prime `p`, every `F : PadicField.{uF} p`, every `T : F.TopologicalData`,
every `hx : BinaryProductExactnessStatement.{uF, uV} F T` and every
`hl : GradedInductionRingLawsStatement F T hx`. The universes `uF` and `uV` stay
independent, and segments and representation carriers live in `max uF uV`, as in
the statement. The theorem has no further hypotheses.

The statement (module `Aubert/ZelevinskyPolynomial`) asserts that
`segmentPolynomialEvaluation F T hx hl` is bijective. This ring homomorphism maps
`MvPolynomial (T.Segment) ℤ` to the graded exact Grothendieck group
`GradedGrothendieckGroup.{uF, uV} F T`, with ring structure
`gradedInductionRing F T hx hl`, and sends each segment variable to the class of its
segment socle (`gradedSegmentSocle`). This is Zelevinsky 1980, Corollary 7.5.

## Proof

The theorem is
`SegmentPolynomialSurjectivity.segmentPolynomialComparison_of_socleExhaustion F T hx hl`
(module `Aubert/SegmentPolynomialSurjectivity`), applied to the published proof
`Classification.multisegmentSocleExhaustion F T` of
`Classification.MultisegmentSocleExhaustion F T` (module
`Classification/MultisegmentSocleExhaustionProof`). That conditional theorem has
exhaustion as its only hypothesis, so the result has no hypothesis beyond the
statement's own parameters. The proof was checked against Library commit
`e0b64667d848b7b76f6f20b029ab4105a635091d`.

The argument of `Aubert/SegmentPolynomialSurjectivity`, described in its Markdown,
runs as follows.

- **Injectivity.** `segmentPolynomialEvaluation_injective_of_derivation` (module
  `Aubert/SegmentPolynomialInjectivity`) is applied to the total derivative ring
  homomorphism `gradedDerivativeRingHom F T ψ hx hl` (module `Aubert/GradedDerivative`),
  using the derivative formulas for segment socles of Zelevinsky 1980, 3.5.
- **Surjectivity.** The proof is by well-founded induction on the strict rank order
  `Multisegment.RankLT` (module `Aubert/MultisegmentRankOrder`). It uses a
  triangularity theorem for this order (a form of Zelevinsky 1980, Theorem 7.1)
  and the weak multiplicity bound "the label count of `a` in `ζ(a)` is at most one"
  (a form of §7.2). Both come from the highest-derivative label step
  `highestDerivativeLabelStep`, which applies
  `ZelevinskyHighestDerivative.exists_label_subquotient` to the published
  homogeneity theorem `Classification.segmentSocleProductHomogeneity` (Zelevinsky
  1980, Theorem 6.2). Exhaustion supplies a multisegment for every irreducible
  representation.
- The unitary additive character `ψ` needed for derivatives comes from the
  published `HarmonicAnalysis.padicUnitaryAdditiveCharacterExists F T`.

## Classification used

The proof uses **Zelevinsky's classification**, specifically only the existence half
of Zelevinsky 1980, Theorem 6.1. The published proposition
`Classification.MultisegmentSocleExhaustion` says that every irreducible smooth
representation of `GL_n(F)` is the unique irreducible subrepresentation of a product
of segment socles, for some multisegment of degree `n`. Neither uniqueness of the
multisegment nor injectivity of `a ↦ ⟨a⟩` is used. The Langlands classification is
not used.

The version used is the published theorem
`Classification.multisegmentSocleExhaustion : MultisegmentSocleExhaustion.{uF, uV} F T`
(Worker 494), whose only parameters are the prime, the field and the topology. For
every rank `n`, including `n = 0`, and every irreducible `π`, it gives a multisegment
`a` with `a.degree = n` and `a.IsZelevinskySocle π`. Here `π` is the unique
irreducible subrepresentation of an actual product of segment socles whose datum
satisfies `IsPrecedenceOrdered`. Its Markdown describes its route: the direct socle argument of Zelevinsky
1980, Theorem 6.1 (c), §6.5 and §6.7. That route starts from a cuspidal embedding,
reduces inversions with the adjacent-swap and linked-reduction rules and integral
twist freeness, and then applies ordered strong-socle existence. The present proof
uses only the weak consequence `IsZelevinskySocle.isZelevinskySubrepresentation`.

## Transitive dependencies

The proof depends, directly or through `Aubert/SegmentPolynomialSurjectivity`, on the
following published declarations and modules.

- `Classification.multisegmentSocleExhaustion` (Zelevinsky 1980, 6.1 (c)).
- `Classification.segmentSocleProductHomogeneity` (Zelevinsky 1980, 6.2).
- `Classification.segmentZelevinskyConstituentExistence`.
- `Classification.SegmentProductCuspidalEmbedding.embedsCuspidal_induced`.
- `HarmonicAnalysis.padicUnitaryAdditiveCharacterExists`.
- The published module `Aubert/GradedDerivative` (the total derivative, its ring
  homomorphism, and the segment formulas `gradedDerivative_segmentSocle_of_length_eq_one`
  and `gradedDerivative_segmentSocle_of_two_le`), `Aubert/MultisegmentRankOrder`
  (the rank order), `Aubert/SupportGrading` (supercuspidal support of labels) and
  `Aubert/SegmentEndDerivation` (`injective_of_endExpansion`, used for injectivity).
- The helper modules `Aubert/SegmentProductClass`, `Aubert/SegmentPolynomialInjectivity`,
  `Aubert/ZelevinskyHighestDerivative` (Worker 237) and
  `Aubert/SegmentPolynomialSurjectivity`.

Their own dependencies are recorded in their Markdown files. The Lean axioms are
`propext`, `Classical.choice` and `Quot.sound`.

## Visible model assumptions

The only assumptions visible in the statement are its parameters `hx` and `hl`.
They are the binary-product exactness proposition and the graded induction ring
laws, and they are used only to form the ring `gradedInductionRing F T hx hl`. The
proof works for arbitrary `hx` and `hl`. The topology on `F` is the supplied
`T.topology`, and induction is the actual normalized parabolic induction of the
Library.
