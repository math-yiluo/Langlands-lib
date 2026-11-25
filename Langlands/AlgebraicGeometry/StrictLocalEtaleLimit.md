# Strictly local affine limits of etale neighbourhoods

`Langlands.AlgebraicGeometry.StrictLocalEtaleLimit S s` packages the following
actual data: a ring in the same universe, a Henselian local ring instance,
a separably closed residue field, a small cofiltered diagram of affine schemes
with etale maps to `S`, and a limiting cone whose point is the spectrum of that
ring. The cone projections commute with a specified map to `S`, and that map
sends the ring's closed point to `s`.

This is an internal interface definition. It asserts neither existence nor a
strict-henselization universal property, and it specifies no residue-field
embedding, flatness of the limit map, or noetherianity. The separate existence
statement can be obtained from a strict henselization, but arbitrary data meeting
these fields may be used.

`level_point_image` proves that each projection of the closed point lies over
`s`, by evaluating compatibility of the cone with the structural maps.
`levelPoint` packages that actual point together with its image equation.
The group-scheme spreading construction is in
`Langlands.GroupScheme.Descent.StrictLocalSpreading`.
