# Strip growth in the continuation of real pair normalizations in the exponents

`RealPairStripReflectionStatement` is the real counterpart of the published
`ComplexPairStripReflectionStatement`. It takes:

- fixed discrete data `sh`, `sh'`;
- holomorphic exponent families `p`, `q` of a complex parameter `z`;
- a real unit `b`, a positive scale `c` and a nonzero `sign`;
- two functions `Z`, `Zd` of `(z, s)`.

It assumes:

- `Z` and `Zd` are jointly holomorphic on the disk `|z| < 3` times a right half-plane
  `σ < Re s`;
- on each closed strip of that half-plane they are bounded uniformly in the disk;
- for every `z` in some small disk around `0`, the pair `Z(z, ·)`, `Zd(z, ·)` has the real
  normalized form with strip growth (`HasRealPairNormalizedGrowth`). This is for the lists
  `blockList sh (p z)`, `blockList sh' (q z)`, their dual lists, the epsilon parameter `b`,
  the scale `c` and the sign.

The conclusion is the same normalized form at the parameter `z = 1`.

## Proof

The proof follows the complex one.

1. `F(z, s)` is the pair reciprocal `L`-factor times `Z`, and `G(z, s)` is the dual pair
   reciprocal `L`-factor times `Zd`. Both are jointly holomorphic on the parameter disk times
   the half-plane (`differentiable_pairDenominator`, using `map_dualBlock_blockList` for the
   dual lists). `E(z, s) = sign · realPairEpsilon(…)(s)` is entire in both variables and never
   zero (`differentiable_pairEpsilon`). `H(z, s) = G(z, 1 - s) / E(z, s)` is holomorphic on
   the parameter disk times the left half-plane `Re s < 1 - σ`.
2. `norm_realEpsilon_eq_of_re_eq` shows that the modulus of the epsilon factor depends only on
   `Re s`. So `E` and `1/E` are bounded on each closed strip uniformly in the parameter disk, by
   compactness of the closed disk times a real interval.
3. `realPairStripRate`, with the strip bounds on `Z` and `Zd`, gives a common rate
   `K = blockCount · π`. With it `F` is bounded by `C exp(K |Im s|)` on closed strips on the
   right, and `H` is bounded the same way on closed strips on the left.
4. For small `z` the given normalized pairs supply the initial data. The one-variable identity
   theorem (`GeneralDirichlet.eqOn_halfPlane`) shows that the entire function `N` agrees with
   `F(z, ·)` on the whole right half-plane. The normalized functional equation shows that it
   agrees with `H(z, ·)` on the left half-plane.
5. The Library's `compactParameterStripGrowth` then gives an entire `N` of exponential strip
   growth with `N = F(1, ·)` on the right and `N = H(1, ·)` on the left.
6. Set `Nd(s) = E(1, 1 - s) · N(1 - s)`. It is entire and has exponential strip growth by the
   strip bound on `E`. It agrees with `G(1, ·)` on the right half-plane because `N = H(1, ·)`
   on the left. By construction `Nd(1 - s) = sign · ε(s) · N(s)` for every `s`.

## Provenance

This is an internal quantitative form of the continuation in the inducing exponents. Jacquet,
*Archimedean Rankin–Selberg integrals* (2009), §8.1, pp. 53–54, uses it to remove the chamber
conditions in the adjacent and equal-rank arguments. It does not assert the hypotheses for any
specific integrals.
