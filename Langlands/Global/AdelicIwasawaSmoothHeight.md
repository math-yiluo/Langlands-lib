# Smooth Iwasawa height on the infinite slices

`IsIwasawaCompact.hasSmoothHeightPairings_of_maximal` gives smooth complex character pairings
on each archimedean slice for any supplied maximal Iwasawa compact. The product decomposition
of a maximal adelic compact splits the Iwasawa covering on the infinite factor. The same product
decomposition and `finiteHeightDisplacement_pair` give `height_pair_of_maximal`, which expresses
the height of an adelic pair as the sum of the heights of its two components.

On the infinite group, let `f` be the continuous character pairing with the height. Left
multiplication by a parabolic point adds its pairing, and right multiplication by an element
of the compact fixes `f`. Average a smooth cutoff equal to one on the compact against its
probability Haar measure. The resulting smooth compactly supported kernel `h` is left invariant
under the compact, nonnegative, and of positive mass. Left invariance of Haar measure rewrites
`∫ h(y) f(xy) dy` using the smooth kernel `h(x⁻¹y)`. Near any `x`, the integration can be restricted
to a fixed compact set, where `compactManifoldIntegrableWeight` gives smoothness. Factoring
`x = pk` and changing variables by `k` also expresses this integral as
`f(x) ∫ h(y) dy + ∫ h(y) f(y) dy`. Solving for `f` proves smoothness. On any other finite slice,
the finite height adds a constant.

This is a consequence of the equivariance of the Library's Iwasawa height. The logarithmic
height convention is the one used for the twist in Bernstein–Lapid, *On the meromorphic
continuation of Eisenstein series* (2024), §2.2 and (2.1), p. 191. The journal PDF
`Bernstein-Lapid--On the meromorphic continuation of Eisenstein series--2024.pdf` is registered
under `bernstein-lapid-2024-meromorphic-continuation-eisenstein` with SHA-256
`6acbe78adf3a7ddff4be0caa92b169f0e609d1245f674a71fbc6989d6aef9268`.
