# Actual single-place embeddings in the standard infinite compact subgroup

For any field `F : Type u` and natural rank `n`, this module constructs
continuous injective group homomorphisms

```text
realPlaceCompactInclusion F n v :
  Matrix.unitaryGroup (Fin n) ℝ →ₜ* standardInfiniteCompact F n
complexPlaceCompactInclusion F n v :
  Matrix.unitaryGroup (Fin n) ℂ →ₜ* standardInfiniteCompact F n.
```

The first source is the actual orthogonal matrix group, using the published
identification of the real unitary condition with orthogonality. The second
is the actual complex unitary group. Their place indices are respectively
the real and complex infinite-place subtypes. All ranks, including zero,
and the arbitrary field universe are allowed. No number-field hypothesis
is needed.

`ArchimedeanCompactFactors.toStandardCompact` views the existing mixed
coordinate product in its original image subgroup. Its underlying map is
the already constructed `toInfiniteAdelicGL`, and its range membership is
the actual image witness. Continuity follows by restriction of the codomain.
The published injectivity of that original map proves injectivity, and
the definition of the standard compact as its image proves surjectivity.

`realPlaceFactor` inserts one orthogonal matrix in its real coordinate,
with identities at all other real and complex coordinates.
`complexPlaceFactor` inserts one unitary matrix in its complex coordinate,
with identities elsewhere. These are homomorphisms by the single-coordinate
and product group constructions. Continuity is checked coordinatewise:
the selected coordinate is the identity map and the other coordinates
are constant. Evaluating at the selected coordinate proves injectivity.

The exported place inclusions compose these factor maps with
`toStandardCompact`, retaining continuity and injectivity. Their matrix
coordinate formulas compute the original completion-based image in the
existing mixed coordinates: the selected matrix appears at its own place
and the matrix identity appears at every other place. Opposite-type
coordinates are explicitly the identity. These formulas use the original
`coordinates_toInfiniteAdelicGL` identity and the actual factor definitions.

This is an internal construction from `ArchimedeanCompact` and pinned
Mathlib's product and single-coordinate group homomorphisms. It uses no
additional original-literature assertion, topology or normalization.
The maps land in the actual standard infinite compact subgroup of the
completion-based general linear group.

No automorphic representation factor, irreducibility, local Langlands
attachment or compatibility between a differentiated local compact action
and a Lie action is asserted by this module.
