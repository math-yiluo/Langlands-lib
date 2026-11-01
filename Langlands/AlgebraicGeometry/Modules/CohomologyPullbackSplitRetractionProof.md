# Split retraction for actual relative-cohomology pullback

This module proves `RelativeCohomologyPullbackSplitRetractionStatement.{u}`
for the published actual `relativeCohomologyPullback`. For arbitrary
commutative `R`, actual schemes `X` and `Y` over `Spec R`, morphisms
`m : Y ⟶ X` and `j : X ⟶ Y` with `w : j ≫ m = 𝟙 X`, an actual
structure-sheaf module `M` on `X`, and every natural degree `n`, the two
successive pullbacks followed by cohomology of the prescribed
`relativeCohomologySplitCoefficientIso m j w` equal the identity.
The only premise is the existing structural equality `w`; degree zero
is included.

This is an internal consequence of the actual composition and identity
laws, proved in `CohomologyPullbackCompositionProof` and
`CohomologyPullbackIdentityProof`. Its coefficient comparison is exactly
the one defined in `CohomologyPullbackSections`; no independent geometric
or cohomological assertion is imported from external literature.

`relativeCohomologyPullback_congr` first handles equality of two morphisms.
After equality elimination, Mathlib's `Scheme.Modules.pullbackCongr` is
the identity isomorphism, so functoriality and composition with the
identity prove the transport equation.

`relativeCohomologyPullback_split` expands the prescribed split coefficient
isomorphism into `pullbackComp`, `pullbackCongr` for the underlying equality
of scheme morphisms, and `pullbackId`. Functoriality expands its cohomology
map into those three maps in that order. The actual composition law
combines the two pullbacks with the first map. The preceding equality
transport lemma turns pullback along `j ≫ m` into pullback along `𝟙 X`.
The actual identity law then cancels the final forward `pullbackId`
coefficient identification. The concluding theorem introduces exactly
the parameters of the published split-retraction proposition and applies
this result.
