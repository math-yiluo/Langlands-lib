# Actual kernels of factored group-scheme homomorphisms

For group schemes `G`, `Q`, and `A` over any scheme `S`, suppose actual
homomorphisms `f : G ⟶ A`, `q : G ⟶ Q`, and `h : Q ⟶ A` satisfy
`q ≫ h = f`. This module defines `FactoredKernel.map f q h fac` from the
scheme-theoretic kernel of `f` to that of `h`. Its composite with the latter
kernel inclusion equals the first kernel inclusion followed by `q`.

`FactoredKernel.isPullback` proves that the square of these two kernel
inclusions with `q` and the new map is a pullback in schemes over `S`.
`isPullback_scheme` gives the square of underlying schemes. Thus the full
scheme kernel of `f` is the inverse image of the full scheme kernel of `h`.
The instances `smooth_map` and `surjective_map` show that smoothness and
scheme surjectivity of `q` pass to this map between kernels. There are no
smoothness or connectedness assumptions on either kernel, and no claim of
surjectivity on the points of each fixed test scheme.

This is a derived construction from the existing actual kernel pullback.
The proof constructs the map using its universal property, pastes the two
kernel squares and cancels the lower square, and then applies stability under
base change. It is a helper for the represented quotient route to split
series; it proves no dimension bound or classification assertion.
