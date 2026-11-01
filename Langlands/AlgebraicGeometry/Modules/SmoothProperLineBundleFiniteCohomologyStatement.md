# Finite line-bundle cohomology on a smooth proper field scheme

`SmoothProperLineBundleFiniteCohomologyStatement` asserts that an actual line
bundle on an actual smooth proper scheme over any field has finite cohomology
in the sense of `DerivedSections.HasFiniteCohomology`. Thus each actual
`relativeCohomology f n` vector space is finite dimensional over the given
field and all sufficiently high cohomology objects are zero.

This is a derived statement from the published `universalPerfectSections`
theorem: over the field it supplies a bounded complex of finite projective
modules representing the actual derived sections. The published
`DerivedPlus.homologyIsoOfIsoDerivedComplex` identifies its homology in
nonnegative degrees with the actual relative sheaf cohomology. Over a field
each homology is finite dimensional, and the representative's upper bound
gives the required eventual vanishing.

The scope includes arbitrary characteristic, disconnected or empty schemes,
and every line bundle. It does not require ampleness, geometric connectedness
or algebraic closure. This file states a proposition; it does not prove it or
assert finite cohomology for arbitrary modules.
