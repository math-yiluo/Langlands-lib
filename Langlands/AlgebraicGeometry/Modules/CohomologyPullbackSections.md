# Elementary comparisons for relative cohomology pullback

These definitions are internal compositions of the Library's relative sections
functor and Mathlib's scheme-module adjunction and composition isomorphisms.
They work in every universe, over any commutative ring `R`, for arbitrary actual
structure-sheaf modules. They impose no geometric or acyclicity hypotheses.
The section and split-coefficient constructions adapt Worker 100's private
`PullbackInterfaceSketch`; that sketch supplied no all-degree pullback map.

For `h : Y ⟶ X` in `Over (Spec R)`,
`DerivedSections.relativePushforwardSectionsIso h` identifies `h_*` followed by
relative global sections on `X` with relative global sections on `Y`. It first
uses the published `relativeGlobalSectionsCompIso h.left X.hom`, whose
construction is the inverse functor associator followed by the whiskered
pushforward-composition isomorphism. It then whisks the pushforward equality
comparison for `h.w : h.left ≫ X.hom = Y.hom` by `moduleSpecΓFunctor`.

`DerivedSections.relativeGlobalSectionsPullback h M` applies relative global
sections on `X` to the actual `pullbackPushforwardAdjunction h.left` unit
`M ⟶ h_* h^* M`, and follows this by the sections comparison evaluated at
`h^* M`. This defines the ordinary section map which fixes the intended
degree-zero normalization for a subsequent derived construction.

For a split pair `m : Y ⟶ X`, `j : X ⟶ Y` and `w : j ≫ m = 𝟙 X`,
`DerivedSections.relativeCohomologySplitCoefficientIso m j w` identifies
`m^* ⋙ j^*` with the identity on `X.left.Modules`. Its three factors are
`pullbackComp j.left m.left`, the pullback comparison for the equality of
underlying scheme maps obtained from `w`, and `pullbackId X.left`.

This module provides only these elementary maps and coefficient identifications.
It constructs no positive-degree cohomology map and asserts no cohomological
identity, composition, degree-zero compatibility, naturality or retraction law.
Its provenance is internal: all three definitions compose existing canonical
operations, with no additional mathematical assertion taken from a source.
