# Ordered Jacquet factors of weak segment quotients

Authors: Worker 485 (the all-shape assembly: coordinate, tensor and transport
lemmas and the induction on the number of blocks) and Worker 1039 (the
unconditional final theorem, integration of the published prerequisites and
the dependency audit). Imported publications keep their own attribution,
including Workers 243 and 485 for the upper tensor construction, Workers 485
and 931 for the conditional weak-head proof, Workers 485 and 949 for the
factor statement, and Workers 485, 429 and 1027 for the flattened comparison.

## Declaration

```lean
theorem Langlands.Classification.segmentQuotientJacquetFactors
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) :
    SegmentQuotientJacquetFactors.{uF,uV} F T
```

This proves exactly the published proposition `SegmentQuotientJacquetFactors`
of `Langlands.Representation.Classification.SegmentQuotientJacquetFactorsStatement`.
It has no hypotheses beyond the statement's telescope. The field universe `uF`
and the base universe `uV` are independent, and the carriers are in
`Type (max uF uV)`. The theorem uses only the axioms `propext`,
`Classical.choice` and `Quot.sound`.

Under `T.topology`, take a segment `Δ` of cuspidal rank `r = Δ.rank` and
length `m = Δ.length`. Take an actual smooth representation `π` of
`GL_(Δ.degree)(F)` with `T.IsSegmentQuotient Δ π`, and an ordered standard
shape `B`. Then either the actual Jacquet carrier `B.JacquetModule π` is a
subsingleton, or the second branch of the statement holds. That branch gives
block lengths `k i > 0` with `B.size i = r * k i` and `∑ k i = m`, the
successive descending subsegments `Γ i`, actual smooth representations `σ i`
of `GL_(B.size i)(F)` whose degree transports are weak quotients of `Γ i`, and
an actual equivalence from the normalized Jacquet representation of `π` along
`B` to the block tensor of the `σ i`.

The module also contains three intermediate public theorems, each with explicit
hypotheses:

- `segmentQuotientJacquetFactors_length_le_two` assumes strong constituent
  existence and the proper two-block head formula. It proves the factor
  alternative for shapes with at most two blocks.
- `segmentQuotientJacquetFactors_of_headFormula` has the same two hypotheses.
  It proves the full statement.
- `segmentQuotientJacquetFactors_of_segmentHeadJacquetFormula` supplies the
  published existence theorem. Its only hypothesis is the head formula.

The final theorem discharges both hypotheses with published theorems.

## Proof

### Final step

`segmentQuotientJacquetFactors` applies
`segmentQuotientJacquetFactors_of_segmentHeadJacquetFormula` to
`segmentHeadJacquetFormula.{uF,max uF uV} F T`. That theorem in turn applies
`segmentQuotientJacquetFactors_of_headFormula` to
`segmentSpecialConstituentExistence.{uF,max uF uV} F T`. Both inputs are
published theorems used at base universe `max uF uV`, the carrier universe of
the target's segments.

### The factor branch

The private `FactorBranch` is exactly the right-hand existential of
`SegmentQuotientJacquetFactors`. It records positive lengths, ranks, the total
length, segment lengths, descending ordered prefix indices, actual block
objects, degree transports, weak quotient relations, and a representation
equivalence over the original block Levi. It assumes no factorization.

### At most two blocks

For a native proper split at `q`, the head formula gives the terminal and
initial heads in that order. Their lengths are `m - q` and `q`, their prefix
sums are `0` and `m - q`, and their base indices are `q` and `0`. Their degree
transports are reflexive. `SmoothRep.equivOfIso` turns the formula's
categorical isomorphism into an actual equivariant linear equivalence
(`factors_split_of_head`). Now take any two-block shape. If its second block
size `l` is not divisible by the cuspidal rank, the formula's zero branch
applies. Otherwise `l = r * q`, and positivity of both blocks gives
`0 < q < m`. `BlockShape.ext_of_size` identifies the shape with the native
segment split while keeping the actual Levi coordinates
(`factors_twoBlock_of_head`).

A weak quotient is first upgraded to a strong head by the published
`segmentWeakQuotientHeadUpgrade`. That theorem takes strong constituent
existence as an explicit premise, and the existence premise is passed on to it
here. The one-block case uses the published
`segmentQuotientJacquetFactors_singleBlock`, including its actual singleton
tensor equivalence. A segment has positive degree, so there is no empty
shape. These cases make up `segmentQuotientJacquetFactors_length_le_two`.

### Ordered comparison and tensor assembly

The ordered comparison (`orderedRefinementJacquetEquiv`) first identifies a
shape with the canonical flattening of a refinement. Its coordinate proof
adapts the private shape-and-label calculation in the published
`Langlands.Representation.Parabolic.RefinementCoordinatesNormalizationProof`.
Because the coordinates are consecutive, the block-label permutation is an
increasing endomorphism of a finite ordinal, hence the identity. Shape
extensionality then identifies the shape itself, and
`FiniteTensor.leviRefinementEquiv_flatten` identifies the actual Levi map. The
second conjunct of the published `Parabolic.flattenedJacquetComparison`, at
universes `0,uF,max uF uV`, and the published intrinsic transitivity clause
give the equivalence from the original Jacquet representation to the iterated
one, pulled back to the original block Levi.

`orderedJacquetTensorEquiv` applies actual Jacquet congruence to the coarse
tensor identification. It then uses the published upper
`RefinedJacquetTensor.jacquetEquiv`, tensors the actual refined factor
equivalences, and applies the inverse of the published
`FiniteTensor.glRefinementEquiv`. The inverse Levi pullback cancels by its
inverse identity. All intermediate representations keep their actual groups
and dependent tensor carriers.

Vanishing of the coarse Jacquet carrier descends through the surjective refined
quotient map `RefinedJacquetTensor.refinedJacquetMk_surjective`. Vanishing of
one refined factor kills the whole indexed tensor: pure tensors span, and
multilinearity applies at the zero coordinate. Ordered comparison, congruence
and the upper tensor equivalence carry the vanishing to the original Jacquet
carrier. The rank transport of the actual Jacquet action is proved by
eliminating the equality. It preserves shape length, block sizes and the
actual Levi definitionally.

### Head and tail

The dependent constructor `headTailCons` combines the unchanged first block
with the actual ordered tail labels. Its total sum is the first value plus the
tail sum. Its prefix is zero at the first block, and at tail label `j` it is
the first value plus the tail prefix at `j`. When the existential data are
extracted, finite sums are stated on canonical finite ordinals, so their
instances keep no semireducible shape-length expressions.

`headTailTensorEquiv` uses the singleton normalized Jacquet tensor equivalence
on the first block and the supplied actual tail equivalence on the remaining
blocks. Dependent family equality is eliminated to transport the tensor
carrier itself. `factors_headTail_step` applies these constructions to the
coarse two-block factor data and the recursive tail result. The coarse base
index of the tail is zero, so the tail segment has the original base and
cuspidal rank. Hence its factor sizes and segment bases rewrite to the
original segment's ranks and descending prefix indices. A zero coarse branch
or a zero tail branch gives the original zero branch.

### Induction

`segmentQuotientJacquetFactors_of_headFormula` uses strong induction on the
number of ordered blocks, generalized over the segment, the representation
and the shape. Shapes with at most two blocks use the base theorem. A shape
with `b > 2` blocks has a two-block head/tail shape and a tail with `b - 1`
blocks. The induction hypothesis is applied to the tail shape transported to
the tail segment's exact degree. The step lemma combines the results, using
the published `Parabolic.normalizedRefinementJacquetTransitivity` for the
coarse head/tail refinement. Thus every ordered block shape is covered.

## Published inputs

All inputs are proved, independently accepted and published Library results,
used by Lean name. The table gives each accepted candidate.

| Lean name | Module | Candidate |
| --- | --- | --- |
| `segmentHeadJacquetFormula` | `Classification.SegmentHeadJacquetProof` | f35f4882 (task 55ad1e10) |
| `segmentSpecialConstituentExistence` | `Classification.SegmentSpecialConstituentExistenceProof` | 2c4a3039 (task 67279e36) |
| `segmentWeakQuotientHeadUpgrade` | `Classification.SegmentWeakQuotientHeadProof` | 3c206426 (task 396dee6d) |
| `segmentQuotientJacquetFactors_singleBlock` | `Classification.SegmentQuotientJacquetSingleBlock` | 34ae0467 |
| `Parabolic.normalizedRefinementJacquetTransitivity` | `Parabolic.RefinementJacquetTransitivityProof` | b11f22a1 (task ec751677) |
| `Parabolic.flattenedJacquetComparison` | `Parabolic.FlattenedJacquetComparisonProof` | f8e6393c (task 35f93465) |
| `RefinedJacquetTensor.jacquetEquiv` | `Parabolic.RefinedJacquetTensor` | 7b878be3 |

All module names are under `Langlands.Representation`. The remaining imports
supply definitions and elementary constructions: block shapes and head/tail
blocks, adjacent-merge shapes, flattened GL refinements
(`FiniteTensor.glRefinementEquiv`, `FiniteTensor.leviRefinementEquiv_flatten`)
and the statement modules.

## Provenance

The all-shape assertion is internally derived, not quoted verbatim. Its
sources are Zelevinsky 1980 (`zelevinsky-1980-induced-ii`), section 9.1,
printed p.197 / PDF p.34, and section 9.5, printed p.198 / PDF p.35, together
with the route of section 3.4, printed pp.181–182 / PDF pp.18–19. In the
source, `m` is the cuspidal rank and `k` the length; here these are `Δ.rank`
and `Δ.length`. Section 9.5 gives the two-block Jacquet module of a segment
head. The passage to arbitrary ordered shapes, by induction on the number of
blocks through Jacquet transitivity, is derived content, as are the head and
tail transports and the use of the weak-quotient upgrade. The proof keeps
the Library's conventions: induction from the upper parabolic with the
positive half-modulus, and Jacquet modules with the inverse half-modulus. It
uses neither the analytic result of section 9.3 nor the conjecture of
section 9.17.

## Dependency audit

The audit covers the transitive `Langlands` import closure of this module at
Library commit `ea837744ab4d479cb0fa59426ead2c2dec4a2f67`, which has 1131 modules. Every closure module
has a nonempty paired Markdown file. Every imported pair is byte-identical to
the Library.

### Independence exclusions

The exclusions are forward special square-integrability
(`SegmentSpecialEssentialSquareIntegrability`, 5eece9e8), ordered conversion
(8252833d), square-integrable exhaustion (cd8ab97c), regular exhaustion
(bf433f0a), `SquareIntegrableLanglandsClassification` (1cb45da2), the
strong-head analytic classification
`SegmentEssentialSquareIntegrableClassification` (aca8805b), tempered block
uniqueness (52e97845), multisegment exhaustion (3bfb61fa), ordered strong-head
existence (ebea9a8a), quotient coverage (20e4e1c6),
`SegmentHeadProductIrreducibility` (8364e73f),
`GenericSegmentProductUniqueness` (30341ae4) and
`MultisegmentSocleExhaustion` (f3a69bc8). Their conclusions, proof successors
and downstream consequences are also excluded.

The closure Lean sources were searched for these names, their task IDs, and
the obvious name variants (exhaustion, coverage, strong-head existence,
tempered uniqueness, segment derivatives). There is exactly one Lean match:
`Classification.RegularLanglandsStatement`. That module contains only the
proposition definitions `GLRegularLanglandsHeadExistenceStatement`,
`GLRegularLanglandsDataUniquenessStatement`,
`GLRegularLanglandsExhaustionStatement` and
`GLRegularLanglandsQuotientStatement`. None of them is proved or assumed in
the closure. It is reached through `Classification.RegularLanglandsHeadReduction`,
which only the shared helper module `Classification.SegmentSocleJacquetReduction`
imports; the head formula's reduction module imports that helper module. Both
modules use only the unconditional lemma
`RegularHeadExistence.nontrivial_normalizedProductInduction` from it, and
neither proves nor assumes head existence or exhaustion. Markdown
matches in the closure are recorded exclusions in other modules' audits, not
inputs.

The closure modules whose names mention tempered, essential,
square-integrable, unitary, analytic, irreducibility or uniqueness objects were
read individually. `Classification.Tempered`, `Classification.Essential`,
`TemperedInductionStatement`, `TemperedSupportStatement`,
`UnitaryGenericCompatibilityStatement`, `RankinSelberg.AnalyticStatement` and
`LanglandsData` hold definitions, elementary lemmas and proposition
definitions; none of these statements is used as a premise. The proved results
among them are general:

- unitarizability from square-integrable coefficients
  (`Unitary.SquareIntegrableProof`);
- continuation of unitarizability (`Unitary.UnitarizabilityContinuationProof`);
- non-unitarizability of `ν^s ρ × ν^(-s) ρ` for large `s`
  (`TwoBlockExponentNonUnitarizabilityProof`);
- factor swapping for irreducible equal-rank products, Zelevinsky 1980 1.9
  (`IrreducibleTwoFactorProductSwapProof`);
- blockwise supercuspidal embeddings (`IrreducibleProductEmbedding`);
- uniqueness of minimal block Weyl representatives and of standard Levi
  refinements (`Geometric.WeylUniquenessProof`, `Geometric.RefinementUniqueness`).

The first three serve the proof of Zelevinsky 1980, 1.11. None of these
results is an excluded conclusion or depends on one. `MirabolicMixedOrbitCoverage*`
and `CompactCoefficient.SelectedCoverage` concern orbits and compact
coefficients, not quotient coverage. No closure module other than this one
imports the factor statement, so the closure has no consumer of the target.

### Derivatives, the analytic result and classification

No derivative statement is a hypothesis of this theorem, and this module
contains no derivative. Derivative theory enters the closure only inside the
premise-free proof of Zelevinsky 1980, 1.11 (`twoSupercuspidalProductStructure`).
The published full cuspidal Jacquet formula `segmentFullJacquetFormula` uses
that proof, and the head formula uses `segmentFullJacquetFormula`. Its nonadjacent
conjunct, `twoSupercuspidalNonadjacentProductIrreducible`, proves BZ77
Theorem 4.2 from general Bernstein–Zelevinsky derivative theory. All 158
closure modules named `Derivative`, `Mirabolic`, `Whittaker` or
`GelfandKazhdan` lie in the closure of
`TwoSupercuspidalNonadjacentIrreducibilityProof`. All of that theory is proved and published in the Library. A trusted
operator decision for the 1.11 task (request
`a8463ee15d57588c8de10306748b2538`) allows such a fully proved route. Its
exclusion list already included the head-formula task 55ad1e10 and this
task's parent 92aea10f. The Markdown of `TwoSupercuspidalProductStructureProof`,
`SegmentFullJacquetProof` and `SegmentHeadJacquetProof` records the audit of
its conditions.

The closure contains no segment derivative statement:
`SegmentSocleDerivatives`, `HighestDerivativeSupportShift` and segment-named
derivative modules are all absent. So the derivative formula of Zelevinsky
1980, 3.5 and 9.6, is neither stated nor used. No classification theorem, and
neither the analytic result of section 9.3 nor the conjecture of section 9.17,
is stated or used. Only the algebraic Jacquet calculations above supply the
factorization.

This audit does not replace independent semantic review.
