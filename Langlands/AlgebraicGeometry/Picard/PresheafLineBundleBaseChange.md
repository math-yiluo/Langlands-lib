# Base change of a representer and its universal bundle

This is an internal construction for polarized scheme descent. The scheme
universe `u` and presheaf value universe `v` are independent.

`representableByBaseChange e p` represents the base restriction of an
arbitrary supplied represented presheaf by the actual fibre product
`N ×_S U → U`. Its natural bijection is the composite of the inverse
adjunction bijection for `Over.map p ⊣ Over.pullback p` and the original
representing bijection. Naturality follows from adjunction naturality
and the naturality of the original representation. The construction reuses
`PresheafLineBundle.baseChangeRepresentation p e` from
`PresheafLineBundleAmpleCover`.

`universalFamily_baseChange` identifies the new universal family with the
restriction of the original one along the adjunction counit, whose
underlying scheme map is the first pullback projection.
`universalBaseChangePullbackIso` applies the specified cartesian identification of
the coherent `PresheafLineBundle` to that equality. It is an isomorphism
of actual line bundles, not an equality of their isomorphism classes.

No sheaf condition or geometric hypothesis is required here. These results
do not assert effective descent, existence of a global representer, or
descent of ampleness.
