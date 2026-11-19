# Real principal-series coefficient extension and inclusion

The expanded list has no induced blocks. Its standard module is the full
principal series of the original position characters. The original standard
module consists of functions in that principal series satisfying the rotation
Fourier conditions. Intersecting with the common space of K-finite functions
gives `realStandardKFinite_le_expand`.

Restricting a uniform coefficient map along an inclusion of K-finite source
spaces preserves its character law, smoothness, growth exponent, and K and Lie
intertwining identities. For two equal source spaces this gives equality of the
spans of the coefficient functions by restriction in both directions. In
particular, all rotation conditions are vacuous when every induced weight is
zero, and `realUniformWhittakerModel_expand_of_zero_weights` proves equality of
the two coefficient spaces for those lists.

`RealUniformPrincipalSeriesExtensionStatement` asks for the extension of each
uniform coefficient map along the source inclusion for lists with at least one
nonzero induced weight. The extension is required to satisfy the uniform
coefficient conditions for the expanded source, with its own polynomial
exponent. Each generating coefficient can then be written using the extension
and the image of its source vector. Taking the supremum of the ranges gives
`RealUniformPrincipalSeriesInclusionStatement` for those lists. The proved model
equality handles the other lists.

The retained premise formulates the coefficient comparison needed to use
Jacquet's extension step in the Library. His Lemma 2.4 extends continuous
Whittaker forms along closed invariant inclusions of Casselman–Wallach
representations. Applying the source theorem requires a comparison between
those continuous forms and the Library's uniform coefficient maps, including
the common source-vector growth condition. The Lean proof here gives the
restriction, zero-weight equality, and conditional implication above.
[Jacquet, §11 and Lemma 2.4](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf)
[Casselman, Hecht, and Miličić, Theorem 8.2 and Corollary 8.3](https://www.math.utah.edu/~milicic/Eprints/whittaker.pdf)
