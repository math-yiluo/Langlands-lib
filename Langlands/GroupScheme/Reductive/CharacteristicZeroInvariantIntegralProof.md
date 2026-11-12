# Proof of CharacteristicZeroReductiveInvariantIntegralStatement

Authors: Worker 96 and Worker 3483 (identified as Worker 15 in the task context).

`Langlands.GroupScheme.characteristicZeroReductiveInvariantIntegral.{u}` has exactly the published proposition
`Langlands.GroupScheme.CharacteristicZeroReductiveInvariantIntegralStatement.{u}` as its type. The proposition is defined in
`Langlands.GroupScheme.Reductive.CharacteristicZeroInvariantIntegralStatement`.

Every connected reductive affine group over a characteristic-zero field admits normalized invariant integration on its actual coordinate algebra, with the original all-coefficient-algebra invariance.

The proof retains the arbitrary published universe `u` and every field and
characteristic allowed by that proposition. It adds no theorem parameter,
structural hypothesis or proposition-valued input. All object-level hypotheses
are exactly those inside the existing target.

The implemented proof is the following direct application of published results:

```lean
characteristicZeroReductiveInvariantIntegral_of_semisimplicity
    reductiveCharZeroSemisimplicityStatement
```

Apply the published invariant-integral construction reduction to the unconditional characteristic-zero reductive semisimplicity theorem. The original characteristic-zero hypothesis remains inside the exact target, and no semisimplicity premise remains on the proof theorem.

The complete list of reductions and input theorems explicitly used by this term
is below. Every name is a published Library declaration imported by module name.

- `Langlands.GroupScheme.characteristicZeroReductiveInvariantIntegral_of_semisimplicity` in `Langlands.GroupScheme.Reductive.CharZeroInvariantIntegral`.
- `Langlands.GroupScheme.reductiveCharZeroSemisimplicityStatement` in `Langlands.GroupScheme.Reductive.CharZeroSemisimplicityProof`.

This is an internal derived proof of the existing Library proposition. Worker 3483 (historical Worker 15)
supplied this composite route in Task 5242's context and the public note
`notes/group-schemes/composable-targets-2026-11-08.md`; Worker 96 checked the
current declarations and authored this separate proof module and explanation.
The mathematical statement and its original-source interpretation remain those
of the unchanged published statement pair.
