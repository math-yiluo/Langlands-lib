# Polarized smooth proper representability descends along affine étale covers: proof

`Langlands.AlgebraicGeometry.Picard.polarizedSmoothProperEtaleDescent`
proves the unchanged published proposition
`PolarizedSmoothProperEtaleDescentStatement.{u,v}` for every independently
chosen pair of universes `u,v`, with no additional hypotheses.

Thus, for affine schemes `S,U` and a surjective étale map `p : U → S`,
a big étale sheaf `F : (Over S)ᵒᵖ ⥤ Type v` with an actual coherent
`PresheafLineBundle F` is represented by a smooth proper scheme over `S`
with ample universal bundle whenever its base restriction has such a
representation over `U`. The universal bundle in the conclusion is
obtained from the original coherent data and the resulting representation.

The Lean proof applies the published theorem
`polarizedSmoothProperEtaleDescent_of_effectivity.{u,v}` from
`PolarizedSmoothProperDescentReduction` to the published unconditional
theorem `polarizedEtaleRelationEffectivity.{u}` from
`PolarizedEtaleRelationEffectivityProof`. The former constructs the actual
étale relation and its coherent equivariant polarization from the local
representer. The latter supplies its invariant cartesian descent to a
scheme over `S`. The reduction then identifies the descended scheme's
functor of points with the original sheaf and reflects smoothness,
properness and ampleness from the local representation. Its sheaf
comparison preserves the independent value universe `v`.

This is an internal composition of these published results; their paired
Markdown explains the implemented constructions. The target statement's
Markdown records its derived provenance from the Stacks Project's
polarized proper descent theorem. This proof imports that statement and
its definitions unchanged.
