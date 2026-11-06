# Actual torus cocycle vanishing from the norm criterion

`Langlands.GroupScheme.dimensionLEOneTorusCocycleVanishing` proves exactly
`DimensionLEOneTorusCocycleVanishingStatement.{u}`. For each field `K : Type u`
satisfying the unchanged `HasDimensionLEOne K`, it gives
`HasTrivialTorusCocycles K`. Thus every actual scheme cocycle of every
`K`-torus on every finite Galois field cover `Spec L` is a coboundary of an
actual point over that same cover, with the equation on every relative test
scheme. No splitting hypothesis on that cover, perfectness, or characteristic
restriction is added.

The implemented proof introduces the fields, field structures, norm
hypothesis, torus and actual cocycle appearing in the two proposition
definitions. It then applies
`IsTorus.cocycle_isTrivial_of_dimensionLEOne` to those exact objects.
That imported theorem splits the torus after extending the original cover,
constructs a common finite Galois normal-closure refinement over `K`, and
applies the norm-based splitting-cover vanishing theorem. Affine fixed-point
descent returns a trivializing point to the original cover, and the proved
finite-Galois value criterion gives the all-test coboundary identity. The
norm-based vanishing step uses the actual field-unit representation tensored
with the transported actual cocharacter lattice and its equivariant
comparison with actual torus points. These are proved imported results,
not additional hypotheses of this theorem.

This proof is a direct internal assembly of the imported actual torus
construction. Worker 1333 authored this assembly and its norm-based torus
construction. The independent structural existence and torus-reduction
results needed for arbitrary connected reductive groups are separate
obligations; this theorem alone does not prove Steinberg quasi-splitness.
