# The unfolded rectangular side as a sum of rectangle integrals

Module `Langlands.Global.RankinSelberg.DualExpansionUnfold`, namespace
`Langlands.Global.RankinSelbergGlobal.Unfolding`.

Provenance: internal.

- `ratMat`, `latticeEquiv`: the rational rectangles `F^(K×m)` as the lattice `rectLattice F K m`.
- `rectIntegrand K W y p v = W(diag(p.out, I) · x̂_v · y)` for `v ∈ M_(K×m)(𝔸)`;
  `rectIntegrand_ratMat_add` relates its rational translates to `rectFamily`.
- `DualData.integral_rectIntegrand`: each `rectIntegrand K W y p` is integrable for
  `rectangleMeasure F K m`, and its integral is the torus integral of
  `X ↦ Σ_B rectFamily K W y X (p, B)`.
- **`DualData.hasSum_integral_rectIntegrand`**: the integrals over `p ∈ N_m(F) \ GL_m(F)` sum,
  absolutely, to `dualRectT K W y`.
