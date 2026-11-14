# Finite length of the actual rational terminal cokernel from dynamic finite length

Module `Langlands.Representation.Aubert.General.RationalSharpFiniteLengthProof`.

Authors:

* Worker 4216: the conditional reduction
  `rationalSharpFiniteLengthStatement_of_dynamic` and its description below.
  It is reused unchanged from the shared draft of Task 4216
  (`0da1c37e-a39a-42e1-b90d-135db6c6e5c3`, revision 1).
* Worker 29, with coauthor Worker 3640 (Task 3640): the statement import and
  the final theorem `rationalSharpFiniteLengthReduction`. Worker 29 rechecked
  the module against Library `c0debd6f4dd02fdd68d70811cf610906b945a962`
  together with the statement module
  [`RationalDetectionFiniteLengthReductionStatements`](RationalDetectionFiniteLengthReductionStatements.md).
* Worker 264: exact-target and protected-import checks for Task 6581, preserving
  the Lean assembly above unchanged.

**Status.** The module is conditional. It proves the published reduction
proposition `RationalSharpFiniteLengthReductionStatement.{u, v}`, which says
that the target `RationalSharpFiniteLengthStatement.{u, v}` follows from the
two dynamic finite-length propositions at carrier universe `max (u + 1) v`.
It does not prove the target unconditionally. The two dynamic propositions are published
but unproved targets of `PrerequisiteStatements`, with their own owner tasks
(`174d2de0-fa21-41b4-b091-f1b86481790b` and
`73e60be8-481a-4cea-b464-eed3bd89be7f`). Once both are proved at independent
universes `u, uV`, the target is this reduction applied to them at
`uV := max (u + 1) v`; Task 4216 owns that final theorem.

## Target of the conditional reduction

`Langlands.Aubert.General.RationalPointFamily.RationalSharpFiniteLengthStatement.{u, v}`
(`RationalSharpConsequenceTargets`). For every nonarchimedean local field `k`,
connected reductive `G`, maximal split torus `i`, generic cocharacter `ν`, the
displayed structural premises `hStandard`, `hOrder`, `hRoots`, closed radicals
`hU`, compact-limit radicals `hUc`, and every linear order on `SimpleRoot i ν`,
it says the following. For every `I` and every finite-length smooth `E` with
carrier in `Type (max (u + 1) v)`, the actual terminal cokernel
`StandardComplex.sharpObject … E I` of the normalized complex has finite
length. This is `SharpFiniteLengthTarget.{u, u, max (u + 1) v}` on the actual
standard families.

## Declarations

### `rationalSharpFiniteLengthStatement_of_dynamic` (Worker 4216)

It takes

- `hiD : DynamicInductionFiniteLengthStatement.{u, max (u + 1) v}` and
- `hr : DynamicJacquetFiniteLengthStatement.{u, max (u + 1) v}`,

and proves `RationalSharpFiniteLengthStatement.{u, v}`.

It introduces every binder of the target exactly as displayed: the field and
its instances, `G`, `hG`, `T`, `i`, `hi`, the local instances (`hG.isAffineHom`,
`hi.isSplitSubtorus.mono`, `pointTopology`), the three topological instances,
`ν`, `hν`, `hStandard`, `hOrder`, `hRoots`, `hU`, `hUc`, the enumeration
`simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν` and the linear
order. It then closes the goal in two published steps.

1. `sharpFiniteLengthTarget_of_inductionJacquet` (`SharpFiniteLength`) proves
   `SharpFiniteLengthTarget.{uI, uG, uV}` for arbitrary families from
   finite-length preservation by every actual normalized composite
   `inductionJacquetFunctor.{uG, max uI uV} (h J) (hclosed J)`. Its proof
   embeds each homogeneous degree of the complex in the finite product of its
   terms `i_J r_J E` and takes the quotient by the incoming differential. It
   uses no exactness of the complex. Here `uI = uG = u` and
   `uV = max (u + 1) v`, so the composite is needed at carrier universe
   `max (u + 1) v`. The arguments `h`, `hclosed`, `hδ`, `hP`, `hU` are
   inferred from the goal; they are the target's
   `isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν`,
   `hU`, `standardUnipotent_isUnimodular i ν hU hUc`,
   `standardParabolic_monotone i ν hOrder hG hi hν` and
   `standardUnipotent_antitone i ν hOrder hG hi hν`.
2. `standardInductionJacquet_preservesFiniteLength_of_dynamic`
   (`RationalStandardFiniteLength`) supplies that premise for every `J`. It
   identifies the standard subgroups of `J` with the rational points of the
   dynamic subgroups of a standard cocharacter chosen from `hStandard`, applies
   the two dynamic statements at carrier universe `max u (max (u + 1) v)`, which
   is `max (u + 1) v`, and composes the two functors.

`hOrder` enters only through the monotonicity proofs fixed by the target;
`hRoots` only through the enumeration; `hUc` only through unimodularity. No
premise is added to the target; the two dynamic statements are hypotheses of
this conditional theorem only.

### `rationalSharpFiniteLengthReduction` (Worker 29)

`theorem rationalSharpFiniteLengthReduction :
RationalSharpFiniteLengthReductionStatement.{u, v}`.

The published proposition
`RationalSharpFiniteLengthReductionStatement.{u, v}` unfolds to the curried
implication

`DynamicInductionFiniteLengthStatement.{u, max (u + 1) v} →
DynamicJacquetFiniteLengthStatement.{u, max (u + 1) v} →
RationalSharpFiniteLengthStatement.{u, v}`.

The proof is the term
`fun hiD hr => rationalSharpFiniteLengthStatement_of_dynamic hiD hr`. The
inputs keep their order and universes, and no premise is added.

## Dependencies

Declarations used by name: `RationalSharpFiniteLengthStatement` (Worker 379,
`RationalSharpConsequenceTargets`); `RationalSharpFiniteLengthReductionStatement`
(`RationalDetectionFiniteLengthReductionStatements`);
`sharpFiniteLengthTarget_of_inductionJacquet` (Worker 508, `SharpFiniteLength`);
`standardInductionJacquet_preservesFiniteLength_of_dynamic` (Worker 749,
`RationalStandardFiniteLength`); `simpleRelativeRootFintype`
(`GroupScheme.Rational.RootFiniteness`); `pointTopology`;
`DynamicInductionFiniteLengthStatement` and `DynamicJacquetFiniteLengthStatement`
(`PrerequisiteStatements`).

The reduction uses no Langlands classification, character independence,
geometric lemma or adjointness result. Any such use enters only through the
proofs of the two dynamic statements, which are not part of this module.

## Sources

The target is the finite-length input needed for Aubert (1995), Corollaire
3.9 (a), printed p. 2189. The two dynamic statements formalize Renard,
*Représentations des groupes réductifs p-adiques* (French edition, 9 July
2026), VI.6.2 (printed p. 178) and VI.6.4 (printed p. 179). Aubert's
Proposition 3.2 is not used. The reduction is an internal relation between
published targets and adds no literature claim. The target pair, the
statement pair and every pair they import are unchanged.
