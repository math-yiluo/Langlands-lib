# Decay of the alternating terms on the truncated sigma region

`arthurAlternatingConstantTermDecay` proves
`ArthurAlternatingConstantTermDecayStatement`, the summand estimate used
after equation (13.7) of Arthur 2005, pp. 71–72. Fix the parabolic,
reflection and Iwasawa height data, a smooth structure, and a matrix
representation of positive size with normalized submultiplicative
adelic height `H`. Take `R ⊆ S ⊆ Δ₀`, a chamber threshold and a
truncation parameter, a compact subset `Ω` of `P₀(𝔸)` and a compact
subset `K'` of `G(𝔸)`.

The input `f` is finite plot-smooth and left `G(F)`-invariant. It has
uniformly moderate growth on the full adelic group, with a single
growth exponent in the adelic source norm for all enveloping-algebra
derivatives and a multiplicative constant that may depend on the
derivative. Let `g` be the signed sum of normalized constant terms
of `f` over `R ⊆ U ⊆ S`, with signs given by the ambient corank.
For each natural order `m`, one constant bounds `|g(p a k)| H(p a k)^m`
uniformly over `p ∈ Ω`, `k ∈ K'` and the positive torus points `a` in the
lower Siegel chamber that satisfy the lower weight truncation and have
shifted relative sigma equal to one. The image of `a` in `G(𝔸)` must
belong to the ambient norm-one group.

The sigma root bounds give a common lower threshold for the simple roots
of the upper Levi and control the height exponentially in the maximum of
zero and the logarithms of the active roots `S \ R`. When the zero
candidate is selected, the order-zero growth estimate applies on the
resulting bounded heights.

For a maximizing active root, the alternating term has a vanishing
ambient maximal constant term. The compact Levi contraction gives
one inverse root scale per derivative order, since the outer radical
fixes the alternating term. The normalized constant-term growth
estimate and finite summation transfer the input's common growth
exponent to the derivative words of `g`. Compactness of the enlarged
right factor set bounds the height at the derivative evaluation points
by a fixed multiple of the torus height. The derivative order absorbs
the common growth exponent and the requested height power. The finitely
many active roots give one bound on the whole region.
