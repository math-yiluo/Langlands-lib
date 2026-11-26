# The real adjacent-rank equation for a split Godement coefficient

Write `H = GL_(r+1)(ℝ)`, `N` for its upper unipotent subgroup, `ι` for the inverse transpose,
`wd = ArchimedeanLocal.dualFunction (r+1)` and `gap` for `r < r + 1`. For a real character datum
`c`, a square Schwartz test `F`, a row Schwartz test `φ` and a function `U` on `H`,
`realAdjacentGodementCoefficient D a (realColumnProduct F φ) U c` is the Godement coefficient on
`GL_(r+2)(ℝ)` of the separated rectangular test `[A | x] ↦ F(A) φ(x)` over `U`. This module proves
the normalized adjacent-rank functional equation, with exponential strip growth, of such a
coefficient against a value of a uniform real Whittaker map, from the corresponding smaller
equal-rank equations. It is the real counterpart of `complexAdjacentSplitGrowth` in the Library's
`ComplexAdjacentSplitEquation`.

## Helper results

- `splitModel_regular`, `splitModel_gauge`, `splitModel_growth`: a function in a uniform real
  Whittaker model is a regular function of its character, satisfies the gauge estimate
  `HasGauge`, and is bounded by a constant times a power of `realMatrixHeight`; all three come
  from `realUniformWhittakerRegularity` (and `RealWhittakerGauge.exists_gauge_bound`).
- `splitPair_invariant`: for `U` regular of character `-a` and `V` regular of character `a`,
  `U(u g) V(u g z) = U(g) V(g z)` for `u ∈ N`.
- `splitModel_minusOne`: for `U` in the uniform model of a block list `ds` of rank `r+1`,
  `U(g · (−1)) = det(ds, −1) U(g)`, from `realUniformWhittakerCentralCharacter`.
- `determinant_characterList_sq`: the determinant sign `det(cs, −1)` of a character list squares
  to one; `determinant_dualCharacterBlocks`: the dual character list
  `RealUniformWhittakerDual.dualCharacterBlocks cs` has the same determinant sign, because
  `c⁻¹(−1) = c(−1)`.
- `realEqualIntegral_dual_reflect`: if the product `wd U · wd V` is left `N`-invariant and
  `wd U(g · (−1)) wd V(g · (−1)) = k · wd U(g) wd V(g)` with `k² = 1`, then
  `realEqualIntegral D (wd U) (wd V) φ s = k · realEqualDualIntegral a D U V (φ̂) s`, where
  `φ̂ = RealGodement.realRowSchwartzFourier (r+1) a φ`. The proof applies
  `RealPlaceReflection.reflection` to the product and recovers `φ` from `φ̂` by row Fourier
  inversion (`RealGodement.realRowSchwartzFourier_neg_comp`).
- `realAdjacentUnfoldedIntegral_expansion`: under the hypotheses of `realAdjacentCompactAverage`
  (`RealAdjacentCompactAverage`), together with a compact expansion
  `∫_K κ(k) V(x iK(k) z) dν(k) = Σ_j W_j(x) C_j(z)` and half-planes of integrability of the
  equal-rank factors of the `W_j` and of the square factors of the `C_j`, the unfolded integral
  `realAdjacentUnfoldedIntegral D η F f U V s` equals
  `Σ_j realEqualIntegral D U (W j) f s · ∫_H realAdjacentMatrixWeight η F s z · C_j(z) dz` on a
  right half-plane. It combines `realAdjacentConvergence`, Fubini, `realAdjacentCompactAverage` and
  `realAdjacentProductExpansion`.

## The split equation

`realAdjacentSplitGrowth` takes:

- real quotient measure data `D` of rank `r`, a compact group `K` with a finite Haar measure `ν`
  and a continuous homomorphism `iK : K → H` onto the orthogonal group;
- a continuous weight `κ` on `K` with finite-dimensional span of left translates;
- `a ∈ ℝˣ`, a real character datum `c`, a square Schwartz test `F` and a row Schwartz test `φ`, such
  that the left translates of `F` and of `F̂ = realRectangularSchwartzFourier a F` by `iK(K)` span
  finite-dimensional spaces, and `κ` reproduces `F` with `c` and `F̂` with `c⁻¹`:
  `∫_K κ(k) c(det iK(k)⁻¹) F(iK(k)⁻¹ A) dν(k) = F(A)` and the same for `F̂` and `c⁻¹`;
- character data lists `cs`, `fs` of length `r+1`, with `ds`, `es` their character block lists, a
  function `U` in `realUniformWhittakerModel r ds (−a)`, a vector `f` of the compact-finite
  standard module of `es` and a uniform real Whittaker map `B` of character `a` on that module;
- the compact projection of `f`: for each `g`, a standard vector `p` with
  `p(iK x) = ∫_K κ(k) f(iK(x) iK(k) g) dν(k)` and `B p(x) = ∫_K κ(k) B f(x iK(k) g) dν(k)`;
- the smaller equal-rank equations: for every `V` in `realUniformWhittakerModel r es a`, the pair
  `realEqualIntegral D U V φ̂`, `realEqualDualIntegral a D U V φ̂` satisfies
  `HasRealPairNormalizedGrowth` for `ds × es` and their duals with parameter `a`, scale `√|a|` and
  sign `det(ds, −1)^r`.

It concludes that, with `W = realAdjacentGodementCoefficient D a (realColumnProduct F φ) U c`, the
pair `realUnequalIntegral gap D W (B f)`, `realUnequalDualIntegral gap (−a) D W (B f)` satisfies
`HasRealPairNormalizedGrowth` for `(character c :: ds) × es` and their duals with parameter `a`,
scale `√|a|` and sign `det(character c :: ds, −1)^(r+1) · det(es, −1)`.

## Proof of the split equation

1. `realLocalCompactProjectionReduction` turns the compact projection of `f` into finitely many
   `W_j` in the uniform model of `es` with character `a` and continuous weights `κ'_j`, with the
   expansions of `∫ κ(k) B f(x iK(k) z)` and of its dual. Put `C_j(z) = ∫_K κ'_j(k) f(iK(k) z) dν(k)`.
2. `realAdjacentSquareGrowth` gives, for each `j`, a half-plane of integrability and the
   normalized equation (sign `1`) of the square pair
   `Z_j(s) = ∫ realAdjacentMatrixWeight c F s z · C_j(z) dz`,
   `Zd_j(s) = ∫ realAdjacentMatrixWeight c⁻¹ F̂ s z · C_j(ι z) dz`.
3. `realEqualPairConvergence` gives half-planes of integrability for the equal-rank factors of
   `(U, W_j)` with the test `φ̂` and of `(wd U, wd W_j)` with the test `φ`; the duals lie in the
   uniform models of the dual character lists by
   `RealUniformWhittakerDual.realUniformWhittakerCharacterDual`.
4. `realAdjacentUnfoldedIntegral_expansion`, applied once to `(F, c, φ̂, U, B f)` and once to
   `(F̂, c⁻¹, φ, wd U, wd(B f))`, expands the two unfolded integrals into finite sums.
5. The Library's `realAdjacentGodementHalfPlane` identifies, on a right half-plane, the ordinary
   unequal integral with `b` times the first unfolded integral, and the dual unequal integral with
   `c((−1)^(r+1)) · b` times the second, where `b = realAdjacentWeylSign r c`.
6. `realEqualIntegral_dual_reflect` rewrites each dual equal-rank factor
   `realEqualIntegral D (wd U) (wd W_j) φ s` as `k · realEqualDualIntegral a D U W_j φ̂ s`, with the
   central sign `k = det(dds, −1) det(dfs, −1)` of the dual lists, which equals
   `det(ds, −1) det(es, −1)` and squares to one.
7. `realAdjacentNormalizedProducts` with `κ = b`, `κd = c((−1)^(r+1)) · b · k` and `sA = det(ds, −1)^r`
   gives the conclusion: `κd · sA = det(character c :: ds, −1)^(r+1) · det(es, −1) · κ` because
   `det(character c :: ds, −1) = c(−1) det(ds, −1)`. The agreement of the normalized sums with the
   unequal integrals holds on the maximum of the half-planes of steps 4 and 5.

## Relation to the literature

H. Jacquet, *Archimedean Rankin–Selberg integrals* (2009), registered as
`jacquet-2009-archimedean-rankin-selberg`, §8.3, pp. 58–60: for `Φ(Y, X) = Φ₁(Y)Φ₂(X)` Jacquet
unfolds `Ψ(s, W, W')` into (8.3) and the dual integral into (8.4), proves the functional equation
formally from the pair `(n − 1, n − 1)` and Proposition 4.4, and makes it rigorous by inserting an
elementary idempotent and expanding into the finite sum on p. 60. The formal proof follows this
route. Its inputs are the Library's unfoldings and convergence results, the smaller equal-rank
normalized equations and a compact projection formula; its analytic conclusion is the Library's
entire normalization with exponential strip growth.
