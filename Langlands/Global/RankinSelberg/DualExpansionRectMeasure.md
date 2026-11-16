# The covolume-one Haar measure on adelic rectangular matrices

Module `Langlands.Global.RankinSelberg.DualExpansionRectMeasure`, namespace
`Langlands.Global.RankinSelbergGlobal.Unfolding`.

Provenance: internal. This is the rectangular version (`k × m` instead of `1 × n`) of the Library
module `EqualAnalyticRowMeasure`, with the same proofs.

- `RectGroup F k m`, the two-block unipotent subgroup with coordinates `M_(k×m)(𝔸)`;
  `rectHomeomorph`, `rectLattice F k m` (the rational matrices), `rectDomain` (the image of the
  Library's fundamental domain).
- `rectangleMeasure_isAddHaarMeasure'`, `isAddFundamentalDomain_rectDomain` and
  `rectangleMeasure_rectDomain` (`rectDomain` has measure one).
- `map_matrixQuotientMap_restrict'`, `integral_eq_integral_periodization'`,
  `lintegral_eq_lintegral_periodization'`: unfolding of integrals over `M_(k×m)(𝔸)` to integrals
  over `M_(k×m)(𝔸/F)` of periodizations.
- `matrixUncurry` and `measurePreserving_matrixUncurry`: `matrixQuotientHaar F k m` corresponds
  to the torus Haar probability on `(𝔸/F)^(k×m)`.
- **`integral_rectangleMeasure_eq_torusIntegral`**: if `Σ_(c ∈ M_(k×m)(F)) f(c + v)` has sum
  `G(v)` for a continuous periodic `G` (in uncurried coordinates), then
  `∫ f d(rectangleMeasure F k m) = T G`; `integrable_of_tsum_norm_le`: `f` is integrable if the
  sums of norms of its translates are uniformly bounded.
