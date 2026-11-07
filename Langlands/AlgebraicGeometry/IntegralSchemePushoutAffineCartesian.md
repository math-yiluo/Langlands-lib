# The canonical affine pinching square is cartesian

This internal construction takes arbitrary commutative rings `R`, `S`, and `T`
in a common universe, maps `f : R → T` and `g : S → T`, and surjectivity of `f`.
The cocone vertex is the spectrum of the actual compatible-pair ring
`f.pullback g`, with arrows given by the spectra of its two projections.
`affineCartesianCocone` bundles this literal cocone with the assertion that
the square with upper vertex `Spec T` and upper arrows `Spec.map f` and
`Spec.map g` is a categorical pullback in schemes.

The proof first establishes `isPushout_pullbackProjections`: the ring square
from the compatible-pair ring to `R`, `S`, and `T` is a categorical pushout.
For a test cocone with maps `a : R → Q` and `b : S → Q`, its compatibility
on the pairs `(r, 0)` for `r` in the kernel of `f` shows that `a` kills that
kernel. Mathlib's descent along a surjective ring homomorphism therefore
produces a ring map `l : T → Q` with `l ∘ f = a`. Every `s : S` has a lift
of `g(s)` through `f`; the corresponding compatible pair then gives
`l(g(s)) = b(s)`. Surjectivity of `f` also proves uniqueness of `l`.

`isPullback_specMap_pullback` applies Mathlib's theorem that the spectrum
of a categorical ring pushout is a categorical scheme pullback. The
cocone commutativity is the spectrum image of the defining compatible-pair
equation. No integrality, finiteness, or nonzero-ring assumption is used.
This is an internal derivation directly from the named Mathlib constructions.
It supplies cartesianness of an affine chart; a scheme pushout universal
property and the global gluing are separate results.
