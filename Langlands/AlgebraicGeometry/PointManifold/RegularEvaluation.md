# Regular-function values on actual affine points

This is an internal interface for the real smooth manifold construction in task
`ab4a68f8-804a-4381-88f6-4f97d57779a7`. The coefficient field is an `RCLike` field
in `Type`, so the constructions include both the actual real and complex fields.
The scheme and its points use the existing `PointTopology.RingPoint` carrier.
There is no new point type and no new topology instance.

`regularEvaluation p` is the algebra map obtained from the published
`affineSchemePointEquiv`. The theorem `regularEvaluation_eq_pullback` identifies
its ring homomorphism with the actual global-section pullback of `p`, followed
by the canonical `Γ(Spec k) ≅ k`. Its proof applies the fully faithful spectrum
functor and the naturality of the canonical affine isomorphism.

`continuous_regularEvaluation` and `continuous_iff_regularEvaluation` restate
the existing evaluation topology through this algebra map.
`regularEvaluation_postcomp` identifies composition of actual relative
morphisms with pullback of regular functions.

`RegularSmooth I f` means that every global regular function has a real smooth
value on the parameter family `f`. Its source model with corners and charted
space are explicit parameters; the definition itself does not need a source
manifold hypothesis. Constants and postcomposition with actual regular maps
preserve this property. This is a property of families, and neither defines
nor assumes a manifold on the target. A later theorem must compare it with
smoothness into a manifold constructed from algebraic smoothness.

The provenance is internal: these definitions combine the published actual
affine-point/global-section comparison with Mathlib's `ContMDiff`. No
algebraic-to-differential comparison is asserted in this file.
