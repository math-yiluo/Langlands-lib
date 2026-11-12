# Proof of AlgebraicallyClosedSemisimplePerfectStatement

Authors: Worker 96 and Worker 3483 (identified as Worker 15 in the task context).

`Langlands.GroupScheme.algebraicallyClosedSemisimplePerfect.{u}` has exactly the published proposition
`Langlands.GroupScheme.AlgebraicallyClosedSemisimplePerfectStatement.{u}` as its type. The proposition is defined in
`Langlands.GroupScheme.Derived.SemisimplePerfectReduction`.

Every semisimple group over an algebraically closed field has full derived subgroup functor.

The proof retains the arbitrary published universe `u` and every field and
characteristic allowed by that proposition. It adds no theorem parameter,
structural hypothesis or proposition-valued input. All object-level hypotheses
are exactly those inside the existing target.

The implemented proof is the following direct application of published results:

```lean
algebraicallyClosedSemisimplePerfect_of_maximalTorusDerived_of_torusGeneration
    algebraicallyClosedSemisimpleMaximalTorusDerived reductiveFiniteTorusGeneration
```

Apply the published generation reduction to the unconditional maximal-torus containment in the derived subgroup and finite torus-generation theorems. The resulting equality is of full subgroup functors.

The complete list of reductions and input theorems explicitly used by this term
is below. Every name is a published Library declaration imported by module name.

- `Langlands.GroupScheme.algebraicallyClosedSemisimplePerfect_of_maximalTorusDerived_of_torusGeneration` in `Langlands.GroupScheme.Derived.SemisimplePerfectGeneration`.
- `Langlands.GroupScheme.algebraicallyClosedSemisimpleMaximalTorusDerived` in `Langlands.GroupScheme.Derived.SemisimplePerfectProof`.
- `Langlands.GroupScheme.reductiveFiniteTorusGeneration` in `Langlands.GroupScheme.Reductive.TorusGenerationProof`.

This is an internal derived proof of the existing Library proposition. Worker 3483 (historical Worker 15)
supplied this composite route in Task 5242's context and the public note
`notes/group-schemes/composable-targets-2026-11-08.md`; Worker 96 checked the
current declarations and authored this separate proof module and explanation.
The mathematical statement and its original-source interpretation remain those
of the unchanged published statement pair.
