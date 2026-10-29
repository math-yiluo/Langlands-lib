# Nonprecedence after one-step initial truncation

Authors: Worker 700 and Worker 684. Worker 700 authored the shared statement
and its initial explanation. Worker 684 reconciled the published prerequisite,
read the original source passages and completed the import and declaration audit.

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
Worker 700 read the original passages, including §6.2 again while preparing
the shared draft. Worker 684 independently read §§3.5, 4.1 and 6.2 as extracted
text and rendered original pages and verified the source fingerprint. No
source-specific errata file was found in the supplied Library or project notes
at submission.

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

The imported `Classification.SegmentInitialTruncation` has independent semantic
acceptance and is published in the Library. Its public constructors keep the
names and types used here. This contribution uses those public definitions;
the earlier combined private compilation of unpublished drafts supplies no
accepted dependency. The present module defines the proposition and supplies
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

The closure contains no conclusion, proof successor or transitive proof
dependency from the following excluded results. This full boundary must be
retained in the separate exact proof task and any lower splits; shared lower
proof inputs require their own independence checks.

| Excluded result | Task or public name |
| --- | --- |
| Ordered-socle existence | `23189526-80b0-4828-a6d4-7ebec2cbeef5` |
| Socle exhaustion | `f3a69bc8-7312-4f82-8a7d-ea3c8188cb63` |
| Analytic segment classification | `aca8805b-054f-4d56-8045-12db7f623404` |
| Unlinked segment-socle product irreducibility | `23e98d90-6055-4e35-91a9-b0f5d8a84961` |
| Final segment-socle irreducibility criterion | `2ae5cbe5-0701-4509-88a0-db8cbeb35be4` |
| Adjacent unlinked segment-socle swap | `AdjacentUnlinkedSegmentSocleSwap` |
| Two-segment socle commutation | `TwoSegmentSocleCommutation` |
| Special-head product irreducibility criterion | `8364e73f-14ec-4d14-8f2b-1555a7c1ce95` |
| Special-head exhaustion | `3bfb61fa-1129-4fc9-83fd-7fcfec22106e` |
| Ordered special-head existence | `ebea9a8a-9b21-4208-aa31-98c2dea1f8a3` |
| Quotient coverage | `20e4e1c6-0f4f-4ca7-96b9-a214ba1a7584` |
| Tempered block uniqueness | `52e97845-36bb-457d-b76f-70753334b88c` |
| Square-integrable Langlands classification | `SquareIntegrableLanglandsClassification`, task `1cb45da2-7007-4351-a694-594fb148b8d1` |
| Square-integrable exhaustion | `cd8ab97c-0b78-4bce-97c4-d307a28159a4` |
| Regular exhaustion | `bf433f0a-921a-428c-b0c0-6475438125ac` |
| Generic segment-product uniqueness | `GenericSegmentProductUniqueness`, task `30341ae4-65f2-4a0e-9283-763db01a409e` |
| Ordered special-segment conversion | `8252833d-c269-41a9-824c-5879e531b23b` |
| Forward special-segment essential square-integrability | `5eece9e8-7f6b-4ea9-abea-a1f9f1b8c807` |
