# The real normalized adjacent-rank equation in a strong chamber

Write `H = GL_(r+1)(ℝ)`, `G = GL_(r+2)(ℝ)` and `gap` for `r < r + 1`. An inducing parameter of
rank `r+2` is a pair `(P, Z)` of parities `P : Fin (r+2) → Fin 2` and exponents
`Z : Fin (r+2) → ℂ`; its character list is `RealGodementProfiles.characterList P Z`, the list of
characters `charData (P i) (Z i)`. `RealGodement.canonicalJacquetMap a P Z` is the canonical
Jacquet map on the compact-finite standard module of this list; it is a uniform real Whittaker
map of character `−a` (`realGodementCanonicalModel`). This module proves the normalized
adjacent-rank equation for canonical values when `Z` lies in the strict chamber and the leading
exponent is large compared with the others. It is the real counterpart of the Library's
`ComplexAdjacentCanonicalChamber`.

## The normalized adjacent-rank subspace

`adjacentGrowthSubmodule D b V xs ys xsd ysd eb c hc sign`, for a fixed function `V` on `H`, is
the set of functions `W` on `G` for which there is `σ` such that for `Re s > σ` the integrands
`realUnequalIntegrand gap W V s` and `realUnequalIntegrand gap (wd W) (wd V) s` (with the duals
`ArchimedeanLocal.dualFunction`) are integrable for `D.measure`, and the pair
`realUnequalIntegral gap D W V`, `realUnequalDualIntegral gap b D W V` satisfies
`HasRealPairNormalizedGrowth xs ys xsd ysd eb c hc sign`. It is a complex submodule: the
integrands are linear in `W` (`realUnequalIntegrand_add'`, `realUnequalIntegrand_smul'`), the
adjacent dual integral is the integral of the dual integrand
(`realUnequalDualIntegral_adjacent`), and `HasRealPairNormalizedGrowth` is closed under sums,
scalar multiples and agreement on a right half-plane.

## Spanning canonical values by split Godement coefficients

- `sectionValue_finset_sum`: under the convergence bound of `realGodementSchwartzMajorant`, the
  real Godement section `RealGodement.sectionValue` is additive in finite sums of Schwartz tests.
- `adjacentSplitGenerators D a P Z`: the functions `W` in the uniform model of
  `characterList P Z` with character `−a` that are of the form
  `realAdjacentGodementCoefficient D a (realColumnProduct (gaussianPolynomial q) φ) U c`, with
  `c = charData (P 0) (Z 0)`, a square polynomial Gaussian test `gaussianPolynomial q`, a row
  Schwartz test `φ`, and `U = canonicalJacquetMap a (Fin.tail P) (Fin.tail Z) f` for a standard
  vector `f` of the tail character list.
- `isCharacterList_characterList`, `characterList_succ` (the list of `(P, Z)` is
  `character c` followed by the list of the tails) and `realStandardKFinite_characterList` (the
  compact-finite standard module of a character list is the compact-finite part of the principal
  series of its position characters).
- `canonicalJacquetMap_mem_span_adjacentSplitGenerators`: if `Z` is in the strict chamber
  `realSpectralChamber (r+1)` and the Godement bound
  `(r+1) + normExponent (realPositionExponent L') (r+1) i ≤ Re Z₀ + (r+2)/2` holds for every
  `i < r+1`, where `L'` is the character list of the tails, then every value
  of `canonicalJacquetMap a P Z` lies in the span of `adjacentSplitGenerators D a P Z`.

  Proof. By `realGodementGaussianSpanning`, the Godement sections `sectionValue` of polynomial
  Gaussian tests over compact-finite vectors `f` of the tail principal series span the larger
  compact-finite module. Expanding the test into its monomials (`gaussianPolynomial_sum_monomials`
  and `sectionValue_finset_sum`) reduces to a monomial test, which splits as
  `realColumnProduct` of a square Gaussian monomial and a column Gaussian monomial
  (`gaussianMonomial_eq_realColumnProduct`). In the chamber the canonical map is the additive
  Jacquet integral (`canonicalJacquetMap_agrees`), and `realGodementSchwartzJoint` identifies the
  Jacquet integral of a Godement section with the Godement coefficient of the test over the
  Jacquet integral of `f`, which is the canonical value of `f` for the tail parameter. Each
  generator is a canonical value, so it lies in the uniform model.

## The equation in the chamber

- `realCompactMatrixTranslate_inverse_of_mem`: for an orthogonal matrix `g`,
  `realCompactMatrixTranslate c⁻¹ Ψ g = realCompactMatrixTranslate c Ψ g`, since `det g = ±1` and
  `c(±1)² = 1`.
- `RealOrthogonalCompactProjectionPremise r`: for every block list `es`, `a ∈ ℝˣ`, continuous weight
  `κ` on the orthogonal group `Matrix.unitaryGroup (Fin (r+1)) ℝ` with finite-dimensional span of
  left translates, uniform real Whittaker map `B` of character `a` on the compact-finite standard
  module of `es`, vector `f` and `g ∈ H`, there is a vector `p` with
  `p(x) = ∫ κ(k) f(x k g) dk` for orthogonal `x` and `B p(x) = ∫ κ(k) B f(x k g) dk` for all
  `x ∈ H`, the integrals taken for the Haar measure `Measure.haar` of the orthogonal group (seen in
  `H` through `Unitary.toUnits`). This module does not prove this statement; it is a hypothesis of
  the results below. `realOrthogonalCompactProjectionPremise` of the module
  `RealOrthogonalCompactProjection` proves it at every rank.
- `realAdjacentCanonicalChamberGrowth`. Assume `RealOrthogonalCompactProjectionPremise r` and
  `RealLocalEqualCharacterGrowthAtRank r`. Let `Z` be in the strict chamber with the Godement bound
  above, `fs` a list of `r+1` character data, `B` a uniform real Whittaker map of character `a` on
  the standard module of `fs` and `v` a vector of it. Then every value
  `canonicalJacquetMap a P Z F` lies in
  `adjacentGrowthSubmodule D (−a) (B v) L es (L.map dualBlock) (es.map dualBlock) a √|a| _ sign`
  with `L = characterList P Z`, `es` the block list of `fs` and
  `sign = det(L, −1)^(r+1) · det(es, −1)`.

  Proof. It suffices to treat the generators. For a generator with polynomial `q`, row test `φ`
  and tail value `U`, apply `realAdjacentSplitGrowth` of `RealAdjacentSplitEquation` with
  `K = Matrix.unitaryGroup (Fin (r+1)) ℝ`, `iK = Unitary.toUnits` and the Haar measure:
  - the left translates of the square test `Ψ = gaussianPolynomial q` and of its Fourier transform
    have finite span (`finiteDimensional_gaussianPolynomial_left`,
    `finiteDimensional_fourier_left`);
  - `exists_realCompactMatrixWeight` gives a continuous weight `κ` with finite left span that
    reproduces `Ψ` with `c`; by `realCompactMatrixTranslate_inverse_of_mem` it reproduces `Ψ` with
    `c⁻¹`, and then `realLocalCompactFourierWeight` shows that it reproduces the transform with
    `c⁻¹`;
  - the compact projection is the premise, and the smaller equal-rank equations come from
    `RealLocalEqualCharacterGrowthAtRank r` at the parameter `−a`, with `−(−a) = a` and
    `√|−a| = √|a|`.
  The integrability clause follows from `realUnequalPairConvergence` for the pair of the generator
  (in the uniform model of character `−a`) and `B v` (of character `a`), and
  `integrable_realUnequalDualKernel_adjacent_iff`. Finally `characterList_succ` matches the lists.

## Relation to the literature

H. Jacquet, *Archimedean Rankin–Selberg integrals* (2009), registered as
`jacquet-2009-archimedean-rankin-selberg`, §8.3, pp. 58–60, proves the equation for the pair
`(n, n − 1)` for the Whittaker functions `W_(Φ,ψ,W₁,μ_n,u_n)` of Godement sections, with `Φ` a
product of a square and a column factor, in the range where the Godement integral converges. The
formal statement spans the canonical values by such sections in the strict chamber using the
Gaussian spanning theorem of the Library, and keeps the compact projection along the orthogonal
group as a named hypothesis.
