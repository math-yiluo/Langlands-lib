# Proof of FlagCoreDualLineStatement

Authors: Worker 96 and Worker 3483 (identified as Worker 15 in the task context).

`Langlands.GroupScheme.flagCoreDualLine.{u}` has exactly the published proposition
`Langlands.GroupScheme.FlagCoreDualLineStatement.{u}` as its type. The proposition is defined in
`Langlands.GroupScheme.FlagCoreDualLine`.

Under the exact flag-core hypotheses over an algebraically closed field, every rational orbit vector admits a nonvanishing linear form whose line is stable under the rational points of the specified subgroup.

The proof retains the arbitrary published universe `u` and every field and
characteristic allowed by that proposition. It adds no theorem parameter,
structural hypothesis or proposition-valued input. All object-level hypotheses
are exactly those inside the existing target.

The implemented proof is the following direct application of published results:

```lean
FlagCore.flagCoreDualLine_of_prerequisites someBorelQuotientProper borelConjugacy
    maximalTorusConjugacy torusFiniteGaloisSplitting solvableProperFixedPoint
```

Apply the published flag-core assembly to unconditional Borel quotient properness, Borel conjugacy, maximal-torus conjugacy, finite Galois splitting of tori and the solvable proper fixed-point theorem. These discharge all five structural inputs. The original stabilizer, spanning and Borel-containment hypotheses remain precisely those already quantified by the target.

The complete list of reductions and input theorems explicitly used by this term
is below. Every name is a published Library declaration imported by module name.

- `Langlands.GroupScheme.FlagCore.flagCoreDualLine_of_prerequisites` in `Langlands.GroupScheme.FlagCoreAssembly`.
- `Langlands.GroupScheme.someBorelQuotientProper` in `Langlands.GroupScheme.Absolute.BorelProperQuotientProof`.
- `Langlands.GroupScheme.borelConjugacy` in `Langlands.GroupScheme.Absolute.BorelConjugacyProof`.
- `Langlands.GroupScheme.maximalTorusConjugacy` in `Langlands.GroupScheme.Absolute.MaximalTorusConjugacyProof`.
- `Langlands.GroupScheme.torusFiniteGaloisSplitting` in `Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof`.
- `Langlands.GroupScheme.solvableProperFixedPoint` in `Langlands.GroupScheme.SolvableProperFixedPointProof`.

This is an internal derived proof of the existing Library proposition. Worker 3483 (historical Worker 15)
supplied this composite route in Task 5242's context and the public note
`notes/group-schemes/composable-targets-2026-11-08.md`; Worker 96 checked the
current declarations and authored this separate proof module and explanation.
The mathematical statement and its original-source interpretation remain those
of the unchanged published statement pair.
