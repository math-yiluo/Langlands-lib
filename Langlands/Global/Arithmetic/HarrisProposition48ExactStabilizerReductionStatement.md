# Reduction of Proposition 4.8 under the exact-stabilizer condition

Module `Langlands.Global.Arithmetic.HarrisProposition48ExactStabilizerReductionStatement`,
namespace `Langlands.Global.Harris`.

The module declares `universe uF uV` and sets `autoImplicit false`. Both
declarations are closed proposition definitions with universes `.{uF, uV}`
and result `Prop`; neither has further outer binders. A rank index `r : ℕ`
in their inputs means `GL_(r+1)`.

Two unproved implications. **Neither is proved here.** They are the
exact-stabilizer counterparts of the published `Proposition48ReductionStatement`
and `Proposition48ReductionTCStatement`: the one-place induction and its named
inputs imply `Proposition48ExactStabilizerStatement.{uF, 0, 0, 0, uV}`, the
restatement of Harris 1998, Proposition 4.8 (printed p.201) with condition
(4.12) on the auxiliary character in place of general position, at the
universes used by globalization.

## `Proposition48ExactStabilizerReductionStatement.{uF, uV}`

The hypothesis is the conjunction of 22 statements, in this order:

1. `Proposition48ExactStabilizerAuxiliaryRankOneStatement.{uF, uV}` (rank one
   with parameters; replaces the published rank-one input);
2. `Proposition48AuxiliaryParityNormalizationStatement.{uF}` (published);
3. `Proposition48AuxiliaryParityUntwistStatement.{uF, uV}` (published);
4. `Proposition48ExactStabilizerParameterUntwistStatement.{uF, uV}` (new);
5. `Proposition48MackeyStepStatement.{uF}` (published);
6. `Proposition48ExactStabilizerMackeyInheritanceStatement.{uF}` and
7. `Proposition48ExactStabilizerParityInheritanceStatement.{uF}` (inheritance
   of (4.12), module `HarrisProposition48ExactStabilizerInheritanceStatement`);
8. `Proposition48ExactStabilizerDistinctnessStatement.{uF, uV}` (new);
9. `Proposition48ExactStabilizerPrimeBranchStatement.{uF, uV}` and
10. `Proposition48ExactStabilizerSingletonBranchStatement.{uF, uV}` (new);
11. `Harris1998Theorem12CuspidalStatement.{0, 0, uV, uV}` (A1);
12. `CuspidalSpectralRigidityStatement.{0, uV}` (C2);
13. `Proposition48IsobaricInvarianceStatement.{uV}`;
14. `CyclicRegularInductionStatement.{0, 0, uV, uV}` (B2);
15. `CyclicRegularOrbitLiftStatement.{0, 0, uV, uV}` (B3);
16. `CyclicStableDescentStatement.{0, 0, uV, uV}` (B1);
17. `CyclicWeakInductionSupercuspidalStatement.{0, 0, uV, uV}` (B4);
18. `CyclicWeakBaseChangeSupercuspidalStatement.{0, 0, uV, uV}` (B5);
19. `TowerBaseChangeHeckeComponentStatement.{0, 0, uV, uV}` (B6);
20. `CyclicPrimeIsobaricBaseChangeStatement.{0, 0, uV, uV}` (Arthur–Clozel
    III.4.2(c));
21. `RestrictedCyclicWeakBaseChangeComplexPlaceStatement.{0, 0, uV, uV}`
    (restricted B7);
22. `CuspidalComplexParameterBridgeTCStatement.{0}` (the archimedean bridge).

Compared with the published reduction: the comparison at a split
supercuspidal place (`HarrisSupercuspidalLocalComparisonStatement`, A2) is
dropped; the published rank-one input and the two branches are replaced by
their parameter-carrying exact-stabilizer forms; inputs 4, 6–8 and 18–22 are added. Inputs 2, 3
and 5 are the published general-position statements, unchanged. They apply to
exact-stabilizer problems because exact-stabilizer validity implies the
published validity
(`IsAuxiliaryExactStabilizerValidAtParity.isAuxiliaryValidAtParity`, through
`generalPositionOfExactStabilizer`), and inputs 6 and 7 upgrade their outputs
back to exact-stabilizer validity. The canonical B7
(`CyclicWeakBaseChangeComplexPlaceStatement`) is not an input.
Every other retained premise and its universe is unchanged, and the relative
order of retained premises is unchanged. The conclusion changes from
`Proposition48Statement.{uF, 0, 0, 0, uV}` to
`Proposition48ExactStabilizerStatement.{uF, 0, 0, 0, uV}`; it does not add a
parameter conclusion to the restated proposition itself.

## `Proposition48ExactStabilizerReductionTCStatement.{uF, uV}`

The conjunction has the same 22 positions, with these exact replacements:

| Position | TC conjunct |
| --- | --- |
| 8 | `Proposition48ExactStabilizerDistinctnessTCStatement.{uF, uV}` |
| 9 | `Proposition48ExactStabilizerPrimeBranchTCStatement.{uF, uV}` |
| 10 | `Proposition48ExactStabilizerSingletonBranchTCStatement.{uF, uV}` |
| 12 | `CuspidalSpectralRigidityTCStatement.{0, uV}` |
| 13 | `Proposition48IsobaricInvarianceTCStatement.{uV}` |
| 14 | `CyclicRegularInductionTCStatement.{0, 0, uV, uV}` |
| 15 | `CyclicRegularOrbitLiftTCStatement.{0, 0, uV, uV}` |
| 16 | `CyclicStableDescentTCStatement.{0, 0, uV, uV}` |
| 17 | `CyclicWeakInductionSupercuspidalTCStatement.{0, 0, uV, uV}` |
| 18 | `CyclicWeakBaseChangeSupercuspidalTCStatement.{0, 0, uV, uV}` |
| 19 | `TowerBaseChangeHeckeComponentTCStatement.{0, 0, uV, uV}` |
| 20 | `CyclicPrimeIsobaricBaseChangeTCStatement.{0, 0, uV, uV}` |

Inputs 1–7, 11, 21, 22 and the conclusion are identical to the ordinary
exact-stabilizer reduction. Compared directly with the published
`Proposition48ReductionTCStatement` in `HarrisProposition48ReductionTCStatement`,
the same additions, replacements and removal listed above are the complete
changes, using the TC versions at the positions shown. Every other premise,
binder and universe is unchanged.

## Why it should hold (proof obligations)

A sketch for the proof task, not a proof. Prove, by strong induction on
`Q.inductionDegree = [L : E]`, that every `Q` with
`Q.IsAuxiliaryExactStabilizerValid` has `Q.HasParameterSolution`.

- If `[E' : E] = 1`, apply input 1 to the published validity.
- Otherwise input 5 gives a prime cyclic step `D`, with one or `[D : E]`
  Mackey classes, and for each `a` a child `R` with published validity at the
  parent's parity and smaller induction degree. Input 6 upgrades it to
  exact-stabilizer validity at that parity. Input 2 gives a parity
  normalization `ν`, `χs` of `R`, and input 7 gives exact-stabilizer validity
  of the corrected problem, which has the same fields and so the same
  induction degree. The induction hypothesis gives it a solution `c` with
  induced parameters. Input 3 gives `S`, `T` with `T.isoClass = c` and
  `R.IsUntwistedSolution ν S T`, and input 4 gives the induced parameters of
  `S`.
- If there is one Mackey class, apply input 10; otherwise apply input 8 for
  distinctness and then input 9. The premises of the branches and of
  distinctness are among inputs 11–22.

Finally, package the data satisfying `IsProposition48ExactStabilizerDatum`
as a problem `Q` and establish `Q.IsAuxiliaryExactStabilizerValid`. Project the
four conditions of `Q.IsSolution` from a parameter solution to obtain the
conclusion of `Proposition48ExactStabilizerStatement`.

## Sources

M. Harris, *The local Langlands conjecture for GL(n) over a p-adic field,
n < p*, Invent. Math. 134 (1998), 177–210, source `harris-1998-local-langlands`,
Proposition 4.8 (printed p.201) and its proof (printed pp.201–203); condition
(4.12) in the proof of Lemma 4.7, printed p.204.

Design: the operator's plan note, source
`operator-external-inputs-plan-2026-11-16`, `external-inputs-plan.tex`,
Section 2.2 (B5–B7, TeX lines 196–199) and Section 4.8 (Remark 4.2, lines
859–894, and lines 897–921). The operator later decided that the
exact-stabilizer branches use the restricted form of B7 with
parameter-carrying solutions, instead of the canonical B7.

The precise decision is the
[operator's R2 ruling](/home/taskhub/pilot/correspondence/a79e2e832569567a8582b3c994f2fc1b.md),
answer to request `c292736a05f55d4fba67d1a01b7fb2e2`. In this design,
regular algebraicity comes from the children's parameters and restricted
B7(2) in the prime branch, restricted B7(1) in the singleton branch, and the
separate bridge. B6 supplies the distinctness of claim (2) of Remark 4.2 in
the plan in place of A2; B5 is claim (3) for a singleton fibre.

The parameter predicates, distinctness and parameter statements packaged by
this reduction are internal interfaces of R2, not statements of Harris. The
reduction is an internal unproved restatement of the published reduction,
and the induction described above is a plan for a later proof. Nothing is
proved here, and no published declaration is changed.
