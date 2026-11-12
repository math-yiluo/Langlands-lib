# Invariant pointed-image generation

Authors: Worker 98 and Worker 3483 (published-input proof route, recorded as Worker 15 in the task context).

`Langlands.GroupScheme.invariantPointedImageGeneration.{u}` proves exactly
`Langlands.GroupScheme.InvariantPointedImageGenerationStatement.{u}`. Its type has no added hypotheses or proposition-valued parameters.

For a pointed morphism from an affine geometrically integral finite-type source into a smooth affine field group, equivariant for the supplied split-torus actions, the fixed closed image envelope has a smooth affine geometrically connected representing group. It carries an actual restricted automorphic action, equivariant inclusion and factor, and an equivariant dominant ordered-product map for some positive power. The field and characteristic remain arbitrary.

The implemented proof uses these published theorems:

- `Langlands.GroupScheme.invariantPointedImageGeneration_of_generation_and_stability` from
  `Langlands.GroupScheme.ImageGenerationStatement`.
- `Langlands.GroupScheme.ImageGeneration.pointedImageGeneration` from
  `Langlands.GroupScheme.ImageGenerationPointed`.
- `Langlands.GroupScheme.pointedImageEnvelopeStability` from
  `Langlands.GroupScheme.ImageEnvelopeStabilityProof`.

Pointed-image generation supplies the representative and a positive dominant power. Envelope stability permits the existing represented-subgroup restriction of the ambient action. The reduction combines the supplied proofs and uses the existing equivariance laws for the inclusion, factor and ordered power map.

The complete proof term is:

```lean
invariantPointedImageGeneration_of_generation_and_stability
    ImageGeneration.pointedImageGeneration pointedImageEnvelopeStability
```

This is an internal derived proof assembling existing Library results along the route recorded for Task 5244. The target statement and its imports are unchanged.
