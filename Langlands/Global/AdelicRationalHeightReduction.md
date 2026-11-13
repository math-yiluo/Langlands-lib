# Rational height reduction from Siegel coverage, norm minimality and central factors

Author: Worker 5152.

This module proves that three propositions together imply the published target
`Langlands.Global.RepresentationGrowth.AdelicRationalHeightReductionStatement`
(module `AdelicRationalHeightReductionStatement`):

- the Siegel covering
  `Langlands.Global.AdelicSiegelFactors.AdelicSiegelReductionStatement`;
- the norm minimality
  `Langlands.Global.AdelicSiegelFactors.SiegelNormMinimalityStatement`;
- the central factor bound
  `Langlands.Global.RepresentationGrowth.CentralNormOneHeightFactorStatement`.

None of the three is proved here. The module also proves three unconditional
lemmas: a height comparison, the triviality of the finite components of positive
torus points, and the compactness of the finite components of weak Siegel products.

The last theorem of the module,
`Langlands.Automorphic.GroupSchemeFunctions.adelicSliceModerateGrowthStatement_of_siegel`,
gives the slice-to-global comparison `AdelicSliceModerateGrowthStatement` from the
same three propositions. It applies the published
`adelicSliceModerateGrowthStatement_of_rationalHeightReduction` (module
`GroupSchemeSliceAdelicGrowthReduction`) to the main result.

## Main result

```lean
theorem adelicRationalHeightReductionStatement_of_siegel
    (hsiegel : AdelicSiegelReductionStatement.{u})
    (hmin : SiegelNormMinimalityStatement.{u})
    (hcentral : CentralNormOneHeightFactorStatement.{u}) :
    AdelicRationalHeightReductionStatement.{u}
```

All four propositions are taken at the same universe `u`.

### Proof

Fix `F`, `G` with `IsAffine G.X.left`, `rho`, `IsConnectedReductive G`,
`IsClosedSubgroup rho` and `0 < N`. The Siegel statement needs the instances
`IsAffineHom G.X.hom` and `LocallyOfFiniteType G.X.hom`. The first is Mathlib's
instance for a morphism between affine schemes. The second follows from the
smoothness field `hG.smooth` of `IsConnectedReductive`.

1. **Data.** The Siegel statement gives a setup `T, i, ν, T₀, j` with
   `IsSiegelAlgebraicSetup`, compact factors `C` and a threshold `t`. Its cover
   predicate gives
   `rationalSubgroup · weakSiegelProduct(canonicalStandardFactors, C, t) = normOneSubgroup`
   as sets. The norm-minimality statement, applied to this setup, `C` and `t`, gives
   `c_m` and `e_m`. The central statement gives `c_z` and `e_z`. The setup's
   derived-torus clause gives a maximal split torus `t₀ : T₀ → D`, so `T₀` is a split
   torus. The lemma `exists_isCompact_finite_weakSiegelProduct` below then gives a
   compact `Ω ⊆ G(𝔸_f)` containing the finite components of all points of the
   product.
2. **One point.** Let `g` be an adelic point. The central statement gives `z` with
   four properties: `z` is central, its finite component is `1`,
   `z⁻¹ g ∈ G(𝔸)¹`, and `adelicHeight(z) ≤ c_z adelicHeight(g)^{e_z}`. The cover
   gives `q₀ ∈ G(F)` and `s` in the Siegel product with `rational(q₀) s = z⁻¹ g`.
   Take `q = q₀⁻¹`. Since `z` commutes with `rational(q)`,
   `rational(q) g = rational(q) z rational(q₀) s = z s`.
3. **Finite component.** `finite(z s) = finite(z) finite(s) = finite(s) ∈ Ω`.
4. **Height.** Write `H` for `adelicHeight` and put `c_z' = max c_z 1` and
   `c_m' = max c_m 1`. Then:
   - `height(infinite(z s)) ≤ H(z s)`, by `height_infinite_le_adelicHeight`;
   - `H(z s) ≤ H(z) H(s)`, by `adelicHeight_mul_le`;
   - `H(s) ≤ c_m H(rational(q₀) s)^{e_m} = c_m H(z⁻¹ g)^{e_m}`, by norm minimality;
   - `H(z⁻¹ g) ≤ H(z) H(g)`, by `adelicHeight_inv`.

   Since `H ≥ 1`,
   `height(infinite(rational(q) g)) ≤ c_m' c_z'^{1+e_m} H(g)^{e_z + e_m (e_z+1)}`.
   The constant is positive.

## Unconditional lemmas

- `AdelicMatrixHeight.mixedSpace_norm_le`: the norm of an infinite adele in the
  mixed space is at most any common bound on its archimedean components. The real
  and complex coordinates are the isometric images of the completion components
  under `extensionEmbeddingOfIsReal` and `extensionEmbedding`.
- `AdelicMatrixHeight.nat_mul_infiniteLocal_le_height`: for positive matrix size `n`,
  each scaled archimedean local maximum `n · infiniteLocal_v(g)` is at most the full
  height `height F n g`. Every factor of the height is at least `1`
  (`one_le_nat_mul_localMaximum`, `one_le_finiteLocal`), and `x ≤ x^{mult}` for
  `x ≥ 1`.
- `AdelicMatrixHeight.norm_archimedean_val_le_height` and
  `AdelicMatrixHeight.matrixHeight_infinite_le_height`: the archimedean matrix
  height `ArchimedeanGL.matrixHeight` of the infinite component of an adelic matrix
  is at most its full height. Every entry of the mixed-coordinate matrix has norm at
  most `height / n`. The `ℓ^∞` operator norm (`Matrix.linfty_opNorm_def`) is a
  maximum of row sums of `n` entries, so it is at most `height`. The inverse follows
  from `height_inv`. The other term of the maximum is `1 ≤ height`.
- `RepresentationGrowth.height_infinite_le_adelicHeight`: for `0 < N`,
  `height F G rho (infinite x) ≤ adelicHeight F G rho x`. The published
  `infiniteMatrix_infinite` (module `GroupSchemeAdelicSliceGrowth`) identifies the
  matrix of the infinite component.
- `AdelicSiegelFactors.evaluation_finite`: the regular-function values of the
  finite component of an adelic point are the finite-adele parts of its values.
- `AdelicSiegelFactors.finite_positiveMap`: for a split torus `T₀`, every
  `positiveMap(a)` has finite component `1`. The published `atFinitePlace_positiveMap`
  gives this at each finite place. `FiniteAdeleRing.ext` and injectivity of
  regular-function evaluation on affine points
  (`affinePointEvaluation_injective`) assemble the places.
- `AdelicSiegelFactors.exists_isCompact_finite_weakSiegelProduct`: for a split
  `T₀`, any standard factor data `D`, compact factors `C` and threshold `t`, the
  finite components of the weak Siegel product lie in the compact set
  `finite(compactPrefix) · finite(K)`. The compact prefix `ι_N(Ω_N) ι_M(Ω_M)` is
  compact as a product of continuous images of compact sets, and the positive
  factor contributes nothing by `finite_positiveMap`.

## Remaining obligations

The slice-to-global comparison now reduces to the three propositions above.

- `AdelicSiegelReductionStatement` is the Siegel covering. Its proof is the
  open task `6adbbc46-4bb2-4c01-843a-d8ded48189f2`, through the good Siegel
  reduction and `adelicSiegelReductionStatement_of_good`.
- `SiegelNormMinimalityStatement` is MW I.2.2 (vii); its Markdown sketches the
  proof.
- `CentralNormOneHeightFactorStatement` is the central factorization, published
  through `adelicPositiveDecompositionStatement`, plus a height bound; its Markdown
  sketches the proof.
