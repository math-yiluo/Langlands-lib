# Proof of ReductiveTorusPowerDominationStatement

Authors: Worker 96 and Worker 3483 (identified as Worker 15 in the task context).

`Langlands.GroupScheme.reductiveTorusPowerDomination.{u}` has exactly the published proposition
`Langlands.GroupScheme.ReductiveTorusPowerDominationStatement.{u}` as its type. The proposition is defined in
`Langlands.GroupScheme.Reductive.TorusDominationReduction`.

Over an infinite field, every connected reductive group receives a scheme morphism with dense image from some finite fiber power of a torus.

The proof retains the arbitrary published universe `u` and every field and
characteristic allowed by that proposition. It adds no theorem parameter,
structural hypothesis or proposition-valued input. All object-level hypotheses
are exactly those inside the existing target.

The implemented proof is the following direct application of published results:

```lean
reductiveTorusPowerDomination_of_generation reductiveFiniteTorusGeneration
    ImageGeneration.pointedImageGeneration
```

Supply the unconditional finite torus-generation and pointed-image generation theorems to the published domination reduction. It constructs the ordered product map and its dense power map. The conclusion is a scheme morphism, with no group-homomorphism requirement.

The complete list of reductions and input theorems explicitly used by this term
is below. Every name is a published Library declaration imported by module name.

- `Langlands.GroupScheme.reductiveTorusPowerDomination_of_generation` in `Langlands.GroupScheme.Reductive.TorusDominationReduction`.
- `Langlands.GroupScheme.reductiveFiniteTorusGeneration` in `Langlands.GroupScheme.Reductive.TorusGenerationProof`.
- `Langlands.GroupScheme.ImageGeneration.pointedImageGeneration` in `Langlands.GroupScheme.ImageGenerationPointed`.

This is an internal derived proof of the existing Library proposition. Worker 3483 (historical Worker 15)
supplied this composite route in Task 5242's context and the public note
`notes/group-schemes/composable-targets-2026-11-08.md`; Worker 96 checked the
current declarations and authored this separate proof module and explanation.
The mathematical statement and its original-source interpretation remain those
of the unchanged published statement pair.
