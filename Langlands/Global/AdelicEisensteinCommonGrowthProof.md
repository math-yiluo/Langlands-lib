# Common growth spaces for regular Eisenstein series

`Langlands.Global.eisensteinCommonGrowth` proves
`Langlands.Global.EisensteinCommonGrowthStatement.{u}` at arbitrary universe `u`. For any
supplied maximal Iwasawa compact and automorphic inducing function, it gives a regularity
threshold and a common finite level and growth exponent for the series on each bounded set
of coordinates. The derivative bound constants may depend on the parameter and the derivative.

## Proof

The elliptic estimate for the inducing slices gives a common exponent `e₀` for the derivatives of
`φ` in the normalized adelic matrix height `H`. Smoothness of the Iwasawa height and the product
estimate for the twist bound each derivative of `φ_λ` by `C H(g)^e₀ |exp ⟨λ, H_P(g)⟩|`.

Choose rational parabolic coset representatives `γ_c` by the polynomial representative
bound, so `H(γ_c) ≤ B h(c)^d₀` for the Chevalley projective height `h(c)`. Choose a nonnegative `t` such
that `∑_c h(c)^(-t)` converges. The regularity threshold is the one for projective decay of
order `d₀ e₀ + t`. It is chosen before the bounded parameter set. At any parameter above the
threshold, apply projective decay to its compact singleton to bound the absolute value of
the height power at `γ_c` by a constant times `h(c)^(-d₀ e₀ - t)`. The polynomial bound for right
translation of the height power gives one exponent `d₁` on the bounded parameter set. Combining
these estimates with submultiplicativity of `H` gives the majorant

\[
C_{D,\lambda} h(c)^{-t} H(g)^{e₀+d₁}
\]

for every enveloping derivative `D` of the Eisenstein term at `γ_c g`.

On each infinite slice, the summable majorant gives locally uniform convergence of every
derivative series. The Library's invariant-derivative limit theorem gives smoothness and
identifies the derivatives of the sum. Summing the majorant gives the common exponent
`R₁ = e₀ + d₁`. Reindexing establishes rational left invariance. Intersect the open finite
stabilizer of `φ` with the finite projection of the maximal Iwasawa compact. This intersection
is compact and open and fixes the twist and every Eisenstein series on the right. The smooth
rational-invariant function gives the growth-space vector. Monotonicity for `H ≥ 1` permits
all exponents `R ≥ R₁`, and the fixed scalar comparison of `H` with the source norm gives the
weight required by `UniformGrowthFrechetSpace`.

## Provenance

- Bernstein and Lapid, *On the meromorphic continuation of Eisenstein series*, JAMS 37 (2024),
  §7.1, pp. 210–211, §8.4, pp. 223–224, and the corollary of §8.6, p. 226. The journal PDF
  `Bernstein-Lapid--On the meromorphic continuation of Eisenstein series--2024.pdf` is registered
  under `bernstein-lapid-2024-meromorphic-continuation-eisenstein` with SHA-256
  `6acbe78adf3a7ddff4be0caa92b169f0e609d1245f674a71fbc6989d6aef9268`. [Journal article](https://doi.org/10.1090/jams/1020)
- The proof uses termwise estimates in the convergence region as in Mœglin–Waldspurger,
  *Spectral Decomposition and Eisenstein Series* (1995), II.1.5, pp. 85–87, with the Library's
  projective-height majorant for arbitrary automorphic inducing data. The registered source
  `moeglin-waldspurger-1995-spectral-decomposition` contains `06.1_pp_78_100_Definitions.pdf`,
  SHA-256 `948dbfd356c2f068c1dc793a52e4c700334eb5236b740f1c775da535b747111c`.
  [Cambridge chapter](https://www.cambridge.org/core/books/abs/spectral-decomposition-and-eisenstein-series/decomposition-according-to-cuspidal-data/5CC739AAD7E91802A81543C76CDC6C57)
