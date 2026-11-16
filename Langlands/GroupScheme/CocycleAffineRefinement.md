# Cocycle triviality from an affine refinement of the base cover

Let `G` be a group scheme over a scheme `S`, and let `ξ` be the published
natural all-test cocycle on an object `U` over `S`. Suppose `r : V → U`
is a morphism over `S` and the structure map `V → S` is quasi-compact,
flat and surjective.

`IsTrivial.of_refine_fpqcCover` proves that a trivialization of `ξ.refine r`
gives a trivialization of `ξ` on the original `U`. It imposes no
surjectivity or flatness condition on `r`, and no covering condition on
`U → S`. To prove it, take the terminal object `P = (S → S)` in the
over category and view `V → S` as a map `s : V → P`.
The published `exists_isTrivialOver` descends the refined cochain to a
relative trivialization on `U ×ₛ P`. Pull that morphism back along the
canonical map `U → U ×ₛ P`. Any two test points have the same image in
`P`, so its relative equation becomes the ordinary coboundary equation.

`fpqcCoverCochain` chooses a resulting point of `G` over `U`.
`fpqcCoverCochain_spec` gives its coboundary equation for every test scheme.
`isTrivial_refine_fpqcCover_iff` combines this reflection with restriction
of a coboundary along `r`.

`isTrivial_of_affine_fppf` works over an affine base and assumes that all
cocycles for `G` on affine, flat, surjective, locally finitely presented
single covers are trivial. For any single fppf cover `U → S`, the
published `affineFppfRefinement` supplies an affine fppf cover `V → S`
mapping to `U`. A morphism between affine schemes is quasi-compact, so
the preceding reflection theorem applies to its trivial refined
cocycle. The resulting triviality is on the original cover `U`,
whose total space need not be quasi-compact.

These are internal deductions from the relative cocycle descent and
affine fppf refinement constructions. They do not assert vanishing for
an arbitrary group scheme: the last theorem consumes vanishing on
affine fppf covers as an explicit hypothesis.
