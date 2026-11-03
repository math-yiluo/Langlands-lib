# Surjective descent of geometric connectedness

`Langlands.AlgebraicGeometry.GeometricallyConnectedSurjectiveDescentStatement`
states that, for arbitrary schemes `X`, `Y`, and `S` in the same universe,
morphisms `f : X → S` and `g : Y → S`, and scheme-surjective `g`,
geometric connectedness of the projection `X ×[S] Y → Y` implies geometric
connectedness of `f`.

Geometric connectedness is Mathlib's property requiring connectedness after
every base change from a field spectrum in that universe. Surjectivity is
surjectivity on underlying scheme points. There are no field-base, flatness,
finite-presentation, smoothness, or openness assumptions.

This is an internal proposition target derived from the existing definitions.
Its intended proof chooses a point of `Y ×[S] Spec K` above a field-valued test
point, passes to its residue field, and descends connectedness along the
resulting surjective field extension. The statement itself contains no proof.
It supplies the geometric descent prerequisite used to pass from a connected
group kernel to connected subgroup preimages in the unipotent-radical quotient
task; it asserts no quotient existence or affineness.
