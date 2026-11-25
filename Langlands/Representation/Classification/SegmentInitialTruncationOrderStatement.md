# Nonprecedence after one-step initial truncation

This module states
`Langlands.Classification.SegmentInitialTruncationOrder.{uF,uV} F T`
as a proposition for every prime, p-adic field and supplied compatible topology.
The field universe `uF` and cuspidal-carrier universe `uV` are independent.
It is a statement definition, not a theorem.

Under the explicit hypothesis
`CuspidalIntegralTwistFreeness.{uF,uV} F T`, it asserts two clauses:

1. If `Δ.dropLast = some Δ'` and `Γ.dropLast = some Γ'`, precedence
   `Δ'.Precedes Γ'` implies `Δ.Precedes Γ`.
2. If the supplied list `l` is nonprecedence ordered, then
   `Segment.dropLastList l` is nonprecedence ordered.

The second clause uses the existing actual list predicate, whose pairwise
condition forbids an earlier segment from preceding a later one. The truncation
list is the existing `filterMap` construction: singleton segments disappear,
and the original order and repeated surviving entries are retained. The
statement includes the empty list. It requires no distinctness or nonemptiness
assumption on the list, and the first clause applies only to the two surviving
nonempty truncations specified by its equalities.

This is internal combinatorial content supporting the induction in Zelevinsky,
*Induced representations of reductive p-adic groups II* (1980), §6.2,
printed p.188 / PDF page 25. The segment and precedence conventions are those
of §4.1, printed p.184 / PDF page 21, and the one-step truncation is from
§3.5, printed p.182 / PDF page 19.
Registered source: `zelevinsky-1980-induced-ii`, SHA256
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
§§3.5, 4.1 and 6.2 were read in the original as extracted
text and rendered original pages, and the source fingerprint was verified. No
source-specific errata file was found in the supplied Library or project notes.

The two clauses are a derived formulation rather than a separate named
theorem quoted from the article. On one free integral twist line, the endpoint
condition for precedence of `[a,b]` and `[c,d]` is
`a < c`, `c ≤ b + 1`, `b < d`. Precedence of the nonempty truncations
`[a,b-1]` and `[c,d-1]` implies those original inequalities. The list clause
then follows by preserving the order of the surviving terms. This explains
the intended elementary proof route; the present module supplies no proof.
In particular, it does not prove the integral-twist-freeness hypothesis.

The project imports are the initial truncation definitions and the
integral-twist-freeness statement. No derivative, homogeneity, socle existence,
product irreducibility or classification conclusion is assumed or asserted.
No support-set deletion identity is included.

The imported `Classification.SegmentInitialTruncation` is published in the
Library. Its public constructors keep the
names and types used here. This module uses those public definitions.
The present module defines the proposition and supplies
no proof of either clause.

## Import independence

The audit follows every project import from both direct imports against Library
commit `9f141aa49982eab63f32f392c4c63dcb83837a19`. All 49 dependency Lean/Markdown
pairs equal the corresponding public Library files. The six classification
dependencies are exactly `ConstituentRelations`,
`CuspidalIntegralTwistFreenessStatement`, `SegmentInitialTruncation`, `Segments`,
`Supercuspidal`, and `SupercuspidalTwist`. In particular, the freeness statement
is imported to give meaning to the explicit hypothesis; its proof is not
imported. The initial-truncation prerequisite itself imports only `Segments`.

The remaining imports provide field normalization, GL and parabolic groups,
smooth representations, actual tensor and induction constructions, twists,
admissibility transport and Jacquet coinvariant definitions. Their proof
modules establish normalization, smooth-vector/pullback properties, elementary
twist algebra and subquotient transport, and admissibility equivalence and
cofinality. They supply no excluded classification conclusion. The actual
induction and constituent relations in `Segments` are definitions; their
presence does not assert an induced-product, derivative or homogeneity theorem.

The complete transitive project dependency list, with the common `Langlands.`
prefix omitted, is:

```text
Group.GL.Basic
Group.GL.Blocks
LocalField.Definitions
LocalField.Canonical
LocalField.Topology
Group.GL.Padic
Group.GL.PadicBlocks
LocalField.Normalization.Definitions
LocalField.Normalization.Statement
LocalField.Normalization.Proof
Group.GL.NormalizedCharacter
Representation.Jacquet.PositiveCharacter
Group.GL.BlockModulus
Representation.Smooth.Definitions
Representation.Category.Basic
Representation.Smooth.SmoothPart.Definitions
Representation.Twist.Definitions
Representation.Induction.Definitions
Representation.Induction.Parabolic
Representation.Smooth.SmoothPart.BasicStatement
Representation.Smooth.SmoothPart.BasicProof
Representation.Smooth.Transfer.PullbackStatement
Representation.Smooth.Transfer.PullbackProof
Representation.Tensor.Finite
Representation.Induction.BlockFactors
Representation.Twist.AdmissibilityStatement
Representation.Twist.SmoothStatement
Representation.Twist.SmoothProof
Representation.Smooth.Admissibility.CofinalStatement
Representation.Smooth.Admissibility.CofinalProof
Representation.Twist.AdmissibilityProof
Representation.Twist.AlgebraStatement
Representation.Twist.AlgebraProof
Representation.Twist.SubquotientDefinitions
Representation.Twist.SubquotientStatement
Representation.Twist.SubquotientProof
Representation.Category.Twist
Representation.Jacquet.Coinvariants
Representation.Smooth.Admissibility.EquivalenceStatement
Representation.Smooth.FixedVectors.Definitions
Representation.Smooth.Admissibility.EquivalenceProof
Representation.Unitary.Basic
Representation.Classification.Supercuspidal
Representation.Twist.RealPower
Representation.Classification.SupercuspidalTwist
Representation.Classification.ConstituentRelations
Representation.Classification.Segments
Representation.Classification.SegmentInitialTruncation
Representation.Classification.CuspidalIntegralTwistFreenessStatement
```

The closure contains no conclusion, proof or transitive proof
dependency from the following excluded results. The proof module
`Classification.SegmentInitialTruncationOrderProof` keeps the same boundary.

| Excluded result | Public name |
| --- | --- |
| Ordered-socle existence | `OrderedMultisegmentSocleExistence` |
| Socle exhaustion | `MultisegmentSocleExhaustion` |
| Analytic segment classification | `SegmentEssentialSquareIntegrableClassification` |
| Unlinked segment-socle product irreducibility | `UnlinkedSegmentSocleProductIrreducible` |
| Final segment-socle irreducibility criterion | `SegmentSocleProductIrreducibility` |
| Adjacent unlinked segment-socle swap | `AdjacentUnlinkedSegmentSocleSwap` |
| Two-segment socle commutation | `TwoSegmentSocleCommutation` |
| Special-head product irreducibility criterion | `SegmentHeadProductIrreducibility` |
| Special-head exhaustion | `MultisegmentHeadExhaustion` |
| Ordered special-head existence | `OrderedMultisegmentHeadExistence` |
| Quotient coverage | `OrderedMultisegmentQuotientExhaustion` |
| Tempered block uniqueness | `TemperedBlockUniqueness` |
| Square-integrable Langlands classification | `SquareIntegrableLanglandsClassification` |
| Square-integrable exhaustion | `SquareIntegrableLanglandsExhaustion` |
| Regular exhaustion | `GLRegularLanglandsExhaustionStatement` |
| Generic segment-product uniqueness | `GenericSegmentProductUniqueness` |
| Ordered special-segment conversion | `OrderedSegmentSquareIntegrableConversion` |
| Forward special-segment essential square-integrability | `SegmentSpecialEssentialSquareIntegrability` |
