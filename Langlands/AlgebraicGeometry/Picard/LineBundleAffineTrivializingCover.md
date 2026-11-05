# Common affine trivializing covers for two line bundles

This internal construction supplies a shared affine open cover for two actual
line bundles on an arbitrary scheme `X : Scheme.{u}`. It is derived from the
published local rank-one definition in `LineBundle`, the ordinary pullback
restriction comparison in `pullbackTrivializationOfLE`, and Mathlib's affine-open
basis for schemes. No external patching theorem is used.

`LineBundle.CommonAffineTrivializingCover L M` records opens indexed by the
points of `X`, their affineness, the equality of their supremum with the top open,
and actual module-sheaf isomorphisms trivializing the pullbacks of both bundles.
The constructor `LineBundle.commonAffineTrivializingCover L M` chooses, at each
point, an affine neighborhood inside the intersection of the two chosen
trivializing opens. Restricting each frame to this smaller open supplies the two
isomorphisms. Every point belongs to its chosen affine neighborhood, which proves
the covering equality.

`LineBundle.exists_commonAffineTrivializingCover` exposes the same construction
as an existential cover indexed by a type in `Type u`, with a nonempty
trivialization for each bundle on every member. The index type is the underlying
point type of `X`. This result imposes no finiteness, separation, base-field or
properness condition and does not assert compatibility between the two frames.
It is a local-cover prerequisite for the separate infinitesimal Picard gluing
proof; it does not itself prove that comparison functor is an equivalence.
