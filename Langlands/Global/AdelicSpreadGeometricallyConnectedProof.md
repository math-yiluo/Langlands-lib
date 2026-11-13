# Geometric connectedness at actual arithmetic integer levels

`Langlands.Global.adelicSpreadGeometricallyConnected` proves
`Langlands.Global.AdelicSpreadGeometricallyConnectedStatement.{u}` for an
arbitrary universe `u`. The statement's source motivation (Conrad,
*Weil and Grothendieck approaches to adelic points*, Theorem 4.5 model step)
and its precise scope are recorded in the statement's paired Markdown. The
Lean proof reuses a complete draft by Worker 208 of the previous project
instance. It uses only the axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Descent along a cofiltered affine limit

`relativeGeometricallyConnectedDescent` works over a cofiltered base diagram
whose transition maps are affine and whose stages are quasi-compact and
quasi-separated. It takes a finitely presented, quasi-compact and
quasi-separated morphism of models, `f : X ⟶ Y`, over `S`, where `Y ⟶ S` is
quasi-compact and quasi-separated. The base change of `f` to the limit is
geometrically connected exactly when its base change to some stage is.

- At each stage, finite presentation, quasi-compactness and
  quasi-separatedness pass to the base-changed morphism. The base-changed
  target is quasi-separated. The published theorem
  `geometricallyConnectedFiberLocalConstructibility`, applied through
  `isConstructible_geometricallyConnectedFiberLocus_of_localConstructibility`,
  then makes that stage's geometric-connectedness fibre locus constructible.
- `geometricallyConnectedFiberLocus_eq_univ_iff` identifies a full locus with
  Mathlib's `GeometricallyConnected`, which includes nonempty fibres.
- `geometricallyConnectedFiberLocus_cone` identifies the limit locus with the
  inverse image of a stage locus along the model cone leg.
- If the limit locus is full, `exists_map_preimage_eq_univ_of_isConstructible`
  gives a transition whose inverse image is full. The cartesian transition
  square (`morphismDiagram_cartesian` with
  `geometricallyConnectedFiberLocus_baseChange`) identifies this inverse image
  with the new stage's locus.
- The converse uses the cartesian cone square.

## The two arithmetic branches

The shared `Langlands.Global.property_baseChangeMap_iff` theorem from
`AdelicSpreadEventualSmoothFiberGeometryProof` uses pullback symmetry to identify the
model-limit base-change maps with the literal over-category base changes
`((Over.pullback p).map f).left` that appear in the target. Any
isomorphism-invariant property is preserved.

`finiteTypeModels_geometricallyConnected_iff_stage` applies the descent to
the spectra of a filtered diagram of algebras over a Noetherian ring `R`.
Locally finite-type, quasi-compact models over `Spec R` are locally
Noetherian. The structure morphism of the source model is therefore locally
of finite presentation, quasi-compact and quasi-separated. The model
morphism inherits these properties by cancellation
(`locallyOfFinitePresentation_of_comp`, `QuasiCompact.of_comp`,
`QuasiSeparated.of_comp`).

This lemma is instantiated with the actual outside-set integer-algebra
diagrams and cocones of the published templates. Noetherianity comes from
`adelicSIntegersNoetherian`. The results are
`curvePlaceSpreadEventualGeometricallyConnected` and
`numberFieldSpreadEventualGeometricallyConnected`. No separatedness,
affineness or pure-dimension condition is imposed on the supplied models.

## Simultaneous smoothness and geometric connectedness

`spectrumIntersection_iff_stage` takes two isomorphism-invariant properties
that are stable under base change, each with its own detection equivalence.
For the forward direction, the two equivalences give stages `i` and `j`.
Pass to the common filtered successor `IsFiltered.max i j`, and transport
each property along its actual cartesian transition square. The converse is
immediate from the two separate equivalences.

This lemma combines the published smoothness detection
(`curvePlaceSpreadEventualSmoothness`, `numberFieldSpreadEventualSmoothness`)
with the geometric-connectedness detection above. The results are
`curvePlaceSpreadEventualSmoothGeometricallyConnected` and
`numberFieldSpreadEventualSmoothGeometricallyConnected`. This step uses no
finite-type premise.

## Compatible models and assembly

The published generic compatible-model theorems
`curvePlaceSpreadMorphismPropertyExistence` and
`numberFieldSpreadMorphismPropertyExistence` are applied to
`@Smooth ⊓ @GeometricallyConnected` with the simultaneous-detection
theorems. They choose separated finite-type source and target models over
an integer level containing the prescribed finite set. They descend the
original field morphism, then enlarge the level until the combined property
holds. They keep the actual generic-fibre isomorphisms and the commuting
square.

Each branch, `curvePlaceSpreadGeometricallyConnected` and
`numberFieldSpreadGeometricallyConnected`, is the triple of its three
clauses. The final theorem pairs the two branches.

The proof uses no common fibre dimension, component choice, Lang–Weil
estimate, integral-point lift or openness result, and it proves none of
these.
