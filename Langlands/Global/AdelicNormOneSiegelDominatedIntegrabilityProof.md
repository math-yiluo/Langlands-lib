# Integrability of Siegel-dominated functions on `G(F) \ G(𝔸)¹`

Module `Langlands.Global.AdelicNormOneSiegelDominatedIntegrabilityProof`.

This module proves the Library statement
`Langlands.Global.NormOneSiegelDominatedIntegrabilityStatement`
(`Langlands/Global/AdelicWeakConstantTermLeviTemperedReduction.lean`):

```
theorem Langlands.Global.normOneSiegelDominatedIntegrability :
    NormOneSiegelDominatedIntegrabilityStatement
```

The theorem has no hypotheses beyond those of the statement; in particular it covers every
matrix representation `rho : MatrixRepresentation G (Fin N)` with `IsClosedSubgroup rho`,
including `N = 0`. It uses only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`.

The statement, its derivation from Delorme and an explanatory route are given in
`AdelicWeakConstantTermLeviTemperedReduction.md`. The proof here does not repeat the
unfolding and Haar-measure estimates of that route. It reduces the statement to the Library's
norm-one chart bound `AdelicSiegelFactors.exists_normOneSiegelIntegralBound` (module
`AdelicNormOneSiegelIntegrability`), which already contains the unfolding onto a Siegel chart,
the cancellation of the modulus against the Haar density and the summation over the chamber. What
is added here are two comparisons of heights at the points of that chart, which turn the
hypothesis `f ≤ δ(a) σ^d` into the hypothesis of the chart bound for `f · σ_{[G]}^{-(d + d₀)}`.

## Sources

- P. Delorme, *On the spectral theorem of Langlands*, Adv. Math. 426 (2023) 109107, registered as
  `delorme-2023-spectral-theorem-langlands` (published PDF, §2, pp. 7–8): the Siegel-domain
  integral (2.5), the comparison (2.7)–(2.8) of the height of a point of a Siegel domain with
  the height of its class, and (2.10); the statement is the integration step of
  Proposition 3.5 (i) ⇒ (ii) (p. 12), as explained in
  `AdelicWeakConstantTermLeviTemperedReduction.md`.
- C. Mœglin and J.-L. Waldspurger, *Spectral decomposition and Eisenstein series* (1995),
  registered as `moeglin-waldspurger-1995-spectral-decomposition`, I.2.2 (vii) (printed
  pp. 20–21): on a Siegel set the norm of a point is bounded by a constant times the norm of
  each of its rational left translates. This is the comparison used in
  `exists_adelicLogHeight_le_mul_rationalLogHeight` below.

## Notation

`F : Type` is a number field and `G` an affine group scheme over `F`, locally of finite type and
connected reductive; `rho : MatrixRepresentation G (Fin N)` is a closed embedding. Write
`‖·‖ = RepresentationGrowth.adelicHeight F G rho`, `σ = adelicLogHeight F G rho` (Delorme's
`σ(x)`) and `σ_{[G]} = rationalLogHeight F G rho` (the quotient height on `G(F) \ G(𝔸)`).
For an algebraic Siegel setup `(T, i, ν, T₀, j)`, compact factors `C` and a threshold `t`,
`A_{T₀}(t) = weakSimpleRootChamber F T₀ T j G i ν t`, and for `a ∈ A_{T₀}`

`siegelRootLogSize i ν j a = 1 + ∑_{α ∈ Δ} |log |α(a)||`

(module `AdelicNormOneSiegelIntegrability`), the sum running over the simple relative roots.
A *chart point* is `X = n m a k w` with `n ∈ Ω_N`, `m ∈ Ω_M` (the images in `G(𝔸)` of the
compact factors of `C`), `a ∈ A_{T₀}(t)` (mapped by `positiveMap`), `k ∈ K = C.compactSubgroup`
and `w` in a finite set `W`; then `s = n m a k` lies in the weak Siegel product
`weakSiegelProduct F G T i ν (canonicalStandardFactors F G T i ν) C T₀ j t`.

## The norm-one chart bound used

`AdelicSiegelFactors.exists_normOneSiegelIntegralBound hG hsetup` gives, for a connected
reductive `G` and an algebraic Siegel setup, compact factors `C`, a threshold `t`, a finite set
`W ⊆ G(𝔸)¹`, an exponent `d₀` and `L < ∞` such that: every measurable left `G(F)`-invariant
`g : G(𝔸) → [0, ∞]` with

`g(n m a k w) ≤ B · siegelModulusNN(a) · siegelRootLogSize(a)^{-d₀}` at all chart points

satisfies `∫_{[G]¹} g(y.out) dy ≤ B L`, the integral being for
`normOneRationalQuotientHaarMeasure F G`. Here `siegelModulusNN` (module
`AdelicSiegelDominatedIntegrabilityProof`) is the `ℝ≥0`-valued modulus, whose real value is
the statement's `siegelModulus` (`coe_siegelModulusNN`).

## Declarations

### Height comparisons on the chart

- `exists_adelicLogHeight_le_mul_rationalLogHeight` (Mœglin–Waldspurger I.2.2 (vii)): for a
  setup, `N > 0`, compact factors `C`, a threshold `t` and a finite set `W`, there is `K ≥ 1`
  with `σ(s w) ≤ K σ_{[G]}(G(F) s w)` for all `s` in the weak Siegel product and `w ∈ W`.
  *Proof.*
  - The published `exists_adelicHeight_map_le_rational_mul` (module
    `AdelicSiegelDiagonalHeightBound`), applied to the split torus `T₀` and `T₀ → T → G`, is
    the diagonal inequality `‖a‖ ≤ c ‖q a‖` for positive points `a` and rational `q`.
    `exists_adelicHeight_le_mul_rational_of_diagonal` (module
    `AdelicSiegelNormMinimalityAssembly`) extends it to the weak Siegel product:
    `‖s‖ ≤ c' ‖q s‖`.
  - With `c'' = max(c', 1)`, a bound `B_W` of `‖w‖ ‖w⁻¹‖` over the finite set `W`, and
    `L = c'' max(B_W, 1) ≥ 1`, submultiplicativity (`adelicHeight_mul_le`) gives
    `‖s w‖ ≤ ‖s‖ ‖w‖ ≤ c'' ‖q s‖ ‖w‖ ≤ c'' ‖q s w‖ ‖w⁻¹‖ ‖w‖ ≤ L ‖q s w‖`.
  - Every `q (G(F) s w).out` is of the form `q₀ s w` with `q₀` rational
    (`out_mk_eq_rational_mul`), so the hypothesis of the published
    `adelicLogHeight_sub_log_le_rationalLogHeight` (module
    `AdelicRationalQuotientSummableLogHeightProof`) holds, giving
    `σ(s w) - log L ≤ σ_{[G]}(G(F) s w)`.
  - Since `σ_{[G]} ≥ 1` (`one_le_rationalLogHeight`), `σ(s w) ≤ (1 + log L) σ_{[G]}(G(F) s w)`.
- `exists_siegelRootLogSize_le_mul_adelicLogHeight`: for a setup, `N > 0`, `IsClosedSubgroup rho`,
  compact factors `C`, a threshold `t` and a finite set `W`, there is `K ≥ 1` with
  `siegelRootLogSize(a) ≤ K σ(X)` at every chart point `X = n m a k w`. *Proof.* For each simple
  root `α`:
  - The published `exists_rootNorm_le` (module `AdelicSiegelDominatedIntegrabilityProof`, which
    uses that `rho` is closed) gives `|α(a)| ≤ C_α ‖a(1, a)‖^{e_α}`, where
    `a(1, a) = siegelTorusMap zc hzc (1, a)` is the image of `a` (`siegelTorusMap_apply`); here
    `zc : Z₀ → T` is the split central torus contained in the setup and `hzc` the centrality of
    `Z₀ → T → G`.
  - The published `exists_adelicHeight_siegelTorusMap_le` (same module) gives `B ≥ 1` with
    `‖a(1, a)‖ ≤ B ‖X‖`, so `t ≤ |α(a)| ≤ C_α B^{e_α} ‖X‖^{e_α}` on the chamber.
  - `abs_log_le_of_mem_Icc` and `log_adelicHeight_le` (same module) give
    `|log |α(a)|| ≤ |log t| + log(C_α B^{e_α}) + e_α (log N^{[F:ℚ]} + σ(X))`, which is at most
    `c_α σ(X)` because `σ(X) ≥ 1` (`one_le_adelicLogHeight`).

  Summing over the finitely many simple roots, `1 + ∑_α |log |α(a)|| ≤ (1 + ∑_α c_α) σ(X)`.
- `mul_pow_mul_inv_pow_le`: an elementary real inequality. If `σ, τ, ρ, K₁, K₂ ≥ 1`, `δ ≥ 0`,
  `σ ≤ K₁ τ` and `ρ ≤ K₂ σ`, then
  `δ σ^d τ^{-(d + d₀)} ≤ K₁^{d + d₀} K₂^{d₀} δ ρ^{-d₀}`. Indeed `τ^{-(d + d₀)} ≤ K₁^{d + d₀}
  σ^{-(d + d₀)}`, `σ^d σ^{-(d + d₀)} = σ^{-d₀}` and `σ^{-1} ≤ K₂ ρ^{-1}`.
- `normOneQuotientInclusion_eq_mk_out`: the image of `y ∈ [G]¹` in `G(F) \ G(𝔸)` is the class
  of its representative `y.out`.

### The theorem

`normOneSiegelDominatedIntegrability_of_pos` treats `N > 0`.

1. *Data.* The setup is the published `siegelAlgebraicSetupExistence_of_structural
   genericMinimalParabolic derivedMaximalSplitTorus derivedCentralSplitTorusProduct`.
   `exists_normOneSiegelIntegralBound` gives `C`, `t`, the finite set `W ⊆ G(𝔸)¹`, `d₀` and
   `L < ∞`. The theorem uses this `C`, `t` and `Ω = W`, which is compact because it is finite.
   Let `K₁`, `K₂` be the constants of the two height comparisons for these data.
2. *Exponent and bound.* For `d : ℕ` take `n = d + d₀` and
   `B = (ofReal(K₁^{n} K₂^{d₀}) · L).toNNReal`, which does not depend on `f`.
3. *The weighted function.* Given `f`, let `g(x) = f(x) · σ_{[G]}(G(F) x)^{-n}`. It is measurable
   (`measurable_rationalLogHeight`, `LeftCosetSpace.measurable_mk`) and left `G(F)`-invariant,
   since `f` is and `G(F) q x = G(F) x` (`LeftCosetSpace.mk_subgroup_mul`).
4. *The chart hypothesis.* At a chart point `X = s w`, the point `s` lies in the weak Siegel
   product (`mem_productSet_iff`), hence in `G(𝔸)¹`
   (`IsSiegelAlgebraicSetup.weakSiegelProduct_subset_normOne`), and `w ∈ W ⊆ G(𝔸)¹`; so
   `X ∈ G(𝔸)¹`. With central factor `1`, `X` is a Siegel point
   (`IsSiegelPoint F G T i ν T₀ j C t W a X`), so the hypothesis of the statement gives
   `f(X) ≤ δ(a) σ(X)^d`. The two comparisons give `σ(X) ≤ K₁ σ_{[G]}(G(F) X)` and
   `siegelRootLogSize(a) ≤ K₂ σ(X)`, and `mul_pow_mul_inv_pow_le` yields
   `g(X) ≤ K₁^{n} K₂^{d₀} · siegelModulusNN(a) · siegelRootLogSize(a)^{-d₀}`.
5. *Conclusion.* The chart bound gives `∫_{[G]¹} g(y.out) dy ≤ ofReal(K₁^{n} K₂^{d₀}) L`. By
   `normOneQuotientInclusion_eq_mk_out`, `g(y.out)` is the integrand of the statement.

`normOneSiegelDominatedIntegrability_of_zero` treats `N = 0`. A closed embedding into `GL_0`
makes `G(𝔸)` a subsingleton (`RepresentationGrowth.isClosedEmbedding_adelicMatrix`). With the
same setup, compact factors `{1}`, `{1}`, `⊥`, threshold `1`, `Ω = {1}` and `n = 0`, the point
`1` is a Siegel point with torus coordinate `1` in `G(𝔸)¹`, so `f(1) ≤ δ(1) σ(1)^d`. Every
representative `y.out` is `1`, so the integral is `f(1)` times the total mass of `[G]¹`, which is
finite by the published
`isFiniteMeasure_normOneRationalQuotientHaarMeasure_of_connectedReductive` (module
`AdelicFiniteVolumeProof`). The bound is `B = (ofReal(δ(1) σ(1)^d) · μ([G]¹)).toNNReal`.

`normOneSiegelDominatedIntegrability` combines the two cases.
