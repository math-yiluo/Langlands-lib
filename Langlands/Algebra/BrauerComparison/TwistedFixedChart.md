# Twisted fixed matrices from a splitting chart

Let `e` be a matrix splitting chart over `L` of a central simple algebra `A`
over `K`. The map `splittingChartEmbedding e` sends `a` to `e(1 ⊗ a)`.
It is injective, and its image spans the matrix algebra over `L`. The spanning
proof uses induction on the tensor product and writes `l ⊗ a` as
`l • (1 ⊗ a)` on pure tensors.

Suppose the chart action at `s ∈ Gal(L/K)` maps `X` to `Pₛ s(X) Pₛ⁻¹`
for a supplied family of invertible matrices `Pₛ`. Let `M` be an extension
of `L` over `K` with `L/K` normal. At `σ ∈ Gal(M/K)`,
`extendedInverseLift` is the entrywise image of `P_(σ|L)⁻¹` in `M`.
For `Y = e(1 ⊗ a)`, the original chart action gives
`Pₛ s(Y) Pₛ⁻¹ = Y`. Thus `Pₛ⁻¹ Y = s(Y) Pₛ⁻¹`.
Enlarging the chart sends `Y` to its entrywise image. Restriction of
automorphisms commutes with that entrywise inclusion, which proves that
the image of `A` in the enlarged chart satisfies the twisted fixed equations.

When `M/K` is Galois, `range_enlargedSplittingChart_eq_twistedFixed` gives
equality between that image and the algebra of all matrices satisfying the
twisted fixed equations. The image spans the enlarged matrix algebra over
`M`. Applying `Algebra.GaloisTwistedMatrix.mem_of_mem_span` to this image
shows that a twisted fixed matrix in its `M`-span already lies in the image.
The equality and injectivity of the embedding give
`twistedFixedEnlargedChartEquiv`, a `K`-algebra equivalence from `A` to
the twisted fixed algebra.
