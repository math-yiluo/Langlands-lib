# The Zariski sheaf of actual relative parabolics

For every reductive group scheme over any base scheme, the
actual parabolic presheaf from `ParabolicPresheaf` is a sheaf for the big
Zariski topology on the slice over that base. Its sections remain the actual
all-test subgroup functors represented by relative parabolic inclusions,
in `Type (u + 1)`; no smallness premise is introduced.

`isMatchingParabolic_of_compatible` identifies ordinary compatible presheaf
sections with `IsMatchingParabolic`. The restrictions in both definitions
are the same actual family restriction. `parabolic_isSheafFor_cover` uses
`existsUnique_restrict` to construct the unique global parabolic family on
every open cover of every parameter scheme. Effective parabolicity is
already proved in the imported matching and descent modules, so this sheaf
result has no additional effectivity assumption.

`parabolic_isSheaf` applies the published general slice-site criterion
`Picard.isSheaf_zariski_over_of_openCover`, which works for type-valued
presheaves in arbitrary value universes. `parabolicSheaf` packages that
same presheaf and the sheaf proof, using Mathlib's equivalence of the
presieve and categorical sheaf conditions for type-valued presheaves.

This is a derived internal result from `ParabolicMatching`, the general
open-cover sheaf criterion, and Mathlib's sheaf definitions. The proof
adapts the compatible-section step of `HomScheme.AdmissibleSheaf` directly
to actual parabolics and uses the existing general criterion to stay on
the slice. It does not assert etale or fppf sheafness, smallness, existence
of a parameter scheme, or smooth proper representability.
