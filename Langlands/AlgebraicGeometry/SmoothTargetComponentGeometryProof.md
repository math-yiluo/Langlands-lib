# Pure fibre geometry on actual target-component restrictions

This proof establishes exactly
`Langlands.AlgebraicGeometry.SmoothTargetComponentGeometryStatement`
in arbitrary common universe `u`, as the theorem
`Langlands.AlgebraicGeometry.smoothTargetComponentGeometry`. The Lean
proof was drafted by Worker 208 of an earlier project instance and is
reused unchanged.

## Full fibre geometry

For the first clause, fix locally Noetherian `Y`, a smooth geometrically
connected `f : X ⟶ Y` and a connected component `c` of `Y`. The proof
rewrites the goal with the published equivalence
`SchemeFiberGeometry.nonemptyGeometricallyConnectedPureDimensionFibers_iff`,
applied to the actual restriction `targetComponentRestriction f c`. That
equivalence says the full fibre predicate holds exactly when the
morphism is geometrically connected and every actual residue-field fibre
has pure dimension equal to the given number. So two facts are needed.

- Geometric connectedness of the restriction comes from the published
  instance `targetComponentRestriction_geometricallyConnected`. That
  instance gets it from Mathlib's instance for the restriction
  `f ∣_ componentOpen Y c`, which is a base change of `f` along the open
  inclusion of the component.
- Pure dimension of every fibre comes from the second conjunct of the
  proved `smoothPureDimension` (`SmoothPureDimensionFibersStatement`).
  It is applied to the restriction, to the selected number
  `smoothTargetComponentDimensions f c`, and to the existing
  specification `smoothTargetComponentDimensions_spec f c`. That
  specification says the restriction is `SmoothOfRelativeDimension` of
  this selected number.

Nonemptiness and fibre dimension are not assumed separately: the
equivalence gets nonemptiness of each fibre from geometric
connectedness. Each component uses its own selected number, so the
dimensions may differ between components. If `Y` is empty, the component
index is empty and the clause holds vacuously; the proof handles that
case without special treatment.

## Finite-type separated structure maps

For the second clause, the source inclusion `componentPreimageι f c` and
the target inclusion `componentι Y c` are inclusions of open subschemes,
and hence open immersions. Instance search then supplies all six required
properties:

- Open immersions are locally of finite type and separated.
- An open immersion into a locally Noetherian scheme is quasi-compact
  (Mathlib, `Mathlib/AlgebraicGeometry/Noetherian.lean`, Stacks 01OX). This
  is where the hypotheses `IsLocallyNoetherian X` and
  `IsLocallyNoetherian Y` are used.
- Composing with the given maps `p` and `q`, which are locally of finite
  type, quasi-compact and separated, preserves each of the three
  properties, by the corresponding composition instances.

No relation between `p`, `q` and `f` is used, matching the statement. No
smoothness or geometric connectedness of `f` is needed for this clause.

## Scope

The proof reuses the published component schemes, restrictions and
selected dimension function; it builds no replacement schemes or
dimension function. It adds no affineness, reducedness, fibre-geometry or
dimension hypothesis. It does not choose arithmetic models, enlarge a set
of places, make dimensions equal across components, prove Lang–Weil or
prove adelic openness.
