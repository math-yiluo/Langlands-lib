# Local compactness of actual full-adele model points

`adelicFixedModelLocalCompactness` proves exactly
`AdelicFixedModelLocalCompactnessStatement` in arbitrary common universe
`u`, for both arithmetic branches. It retains the actual relative scheme
points, their original outside-`S` scalar actions and precisely the final
topologies named in the statement.

The proof first establishes the properties of each fixed-base stage.
The model at a finite superset `T` is the actual pullback of `X`.
Local finite type and quasi-compactness are preserved by this pullback;
separatedness is preserved when it is assumed. The arithmetic-level
theorem `adelicLevelModelLocalCompactness` therefore gives local compactness
and conditional Hausdorffness of the base-changed model's level points.
The existing `curvePlaceFixedModelPointHomeomorph` and
`numberFieldFixedModelPointHomeomorph` transport these properties to the
fixed-base stage spaces with their stated topologies.

For the full point space, the proof applies the published
`filteredRingPointTopologicalComparison` to the actual fixed-base algebra
diagram and its actual full-adele cocone. The cocone's algebra colimit
property is supplied by `curvePlaceAdeleOverIsColimit` or
`numberFieldAdeleOverIsColimit`. Noetherianity of the actual outside-`S`
integer base upgrades local finite type to local finite presentation.
Thus the filtered theorem applies to actual scheme points rather than
to an assumed point presentation.

`adelicFixedModelTransitionTopology` supplies continuity and openness of
each actual coefficient change. The filtered theorem then transfers
stage local compactness to the full point space's final topology. Its
argument maps compact neighbourhoods in stages to compact
neighbourhoods by the continuous open stage maps; it needs no separation
premise. When `X` is separated, the same arithmetic transition theorem
gives open embeddings and hence injective transitions. Together with
the Hausdorff stage properties, the filtered theorem gives Hausdorffness
of the full point space.

Finite constants and the compatible rational-function scalar tower are
retained in the function-field clause, with no separability premise.
Every infinite completion is retained in the number-field clause.
No step imposes nonempty `S`, affine models or separatedness for local
compactness.

This implements the arithmetic-stage and direct-limit argument of Brian
Conrad, *Weil and Grothendieck approaches to adelic points* (December 31,
2011), printed page 9, Corollary 3.7 and the beginning of Section 4.
As explained in the target's Markdown, the fixed-model formulation,
nonseparated local compactness and the allowance of empty `S` are derived
extensions. The proof does not supply generic-fibre descent, model
independence, second countability or the other assertions of Section 4.

Source: registered literature `conrad-2011-weil-grothendieck-adelic-points`,
SHA-256 `fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`,
printed page 9.
