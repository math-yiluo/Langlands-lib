# Absolute convergence of adelic Eisenstein series

`Langlands.Global.eisensteinAbsoluteConvergence` proves
`Langlands.Global.EisensteinAbsoluteConvergenceStatement.{u}`. For the
supplied Iwasawa compact subgroup and automorphic function, it gives a
regularity threshold `R` and a summable majorant on `P(F) \ G(F)` for each
compact set of adelic arguments and each compact set of `R`-regular
parameters in the supplied linear coordinates.

## Proof

`Chevalley.exists_line_stabilizer` supplies a representation `σ` and a
coordinate line with exact stabilizer `P`. The injective map
`parabolicRationalProjectiveEmbedding` sends `P(F)g` to the line obtained by
acting on that coordinate line by `σ(g⁻¹)`. Write `H(c)` for the
multiplicative Weil height of the resulting projective point.

`exists_polynomial_rationalCoset_representatives` constructs a rational
representative `x` of each `c` whose lower-bounded adelic matrix height is at
most `B H(c)^d` for fixed `B > 0` and `d ≥ 0`. It realizes the same line orbit
as a closed projective embedding of `G/P`. Translates of the opposite
cell give local sections of the quotient projection. A finite cover of
its rational points by basic opens in projective charts lets the proof
bound the section's matrix and inverse-matrix entry heights in terms of
the projective coordinate ratios. The local matrix height comparison and
the finite cover give the fixed coefficient and exponent. The section is
applied to the image of `g⁻¹` in `G/P`. Inverting its lift gives the
representative of `P(F)g` and preserves the matrix-and-inverse height.

The automorphic predicate supplies left invariance under `U(𝔸)M(F)` and
moderate growth. The rational Levi decomposition and the product formula
identify the Eisenstein term on any rational representative, so the
majorant theorem can evaluate it at the bounded representative. Compact
right translation and moderate growth bound the norm of the function there
by a constant times `H(c)^(d r₀)` for a fixed growth exponent `r₀ ≥ 0`.

The regular parameter decay theorem identifies the real parameter pairing
on the split component. The Iwasawa functional vanishes on ambient
characters at rational points, and the determinant characters of containing
parabolics give the lower bounds needed for the root-cone estimate.
The logarithmic Chevalley orbit height bound and compactness of the parameter
set then give any prescribed inverse power of `H(c)` for sufficiently
regular parameters. The compact Iwasawa translation bound extends this
estimate to the adelic arguments in the given compact set.

Polynomial counting of number-field scalar heights gives an exponent `t`
for which the inverse `t`-th power of projective height is summable. The proof
asks for twist decay with exponent `d r₀ + t` and takes the corresponding
regularity threshold before fixing either compact set. Multiplication with
the growth bound leaves a constant times `H(c)^(-t)`. Pullback along the
injective projective coset map preserves summability, yielding the majorant
of `IsIwasawaCompact.exists_summable_eisenstein_majorant_of_projectiveRepresentatives`.

## Provenance

The normal convergence conclusion corresponds to Mœglin and Waldspurger,
*Spectral decomposition and Eisenstein series* (1995), II.1.5, p. 85, and
Bernstein and Lapid, *On the meromorphic continuation of Eisenstein series*
(2024), §2.2, p. 191. The Lean proof uses a direct projective height argument.
The proof combines the polynomial representative comparison and
number-field height counting with the adelic Iwasawa and parabolic root
estimates in the accompanying modules.
