# Last-row coordinates of real unipotent quotients

Module `Langlands.Global.RankinSelberg.RealLowerBlockChart`. Helper declarations are in the namespace
`Langlands.Global.RankinSelbergGlobal.RealLowerBlockChart`; the statement and its proof are in
`Langlands.Global.RankinSelbergGlobal`.

Write `G_m = GL_m(ℝ)`, `N_m` for its upper unitriangular subgroup, `B⁻_m` for the invertible lower
triangular matrices (`lowerTriangularSubgroup m ℝ`) and `Q_n = N_(n+1) \ G_(n+1)`
(`LeftUnipotentQuotient n ℝ`). Quotient measure data `D : RealQuotientMeasureData n` consist of Haar
measures on `G_(n+1)` and `N_(n+1)` and a compatible quotient measure `D.measure` on `Q_n`
(Weil formula, module `QuotientMeasure`).

## Statement

`RealLastRowChartStatement`: for every `n`, all `D : RealQuotientMeasureData n` and
`D' : RealQuotientMeasureData (n + 1)`, there is a real `C > 0` with

`D'.measure = ofReal C • (lastRowMeasure n D).map (lastRowChart n)`.

Here

- `lastRowChart n ([g], x, u) = [[[g, 0], [x, u]]]` for `[g] ∈ Q_n`, a row `x ∈ ℝ^(n+1)` and `u ∈ ℝˣ`:
  the coset in `Q_(n+1)` of the block matrix with upper left block `g`, last row `(x, u)` and zero
  last column above `u`. It is the Library's `lowerBlockQuotientChart` (module
  `LowerBlockQuotientCoordinates`) with `d = 1`, composed with `rowEquiv : ℝ^(n+1) ≃ M_(1×(n+1))(ℝ)`
  and `unitsLower : ℝˣ → B⁻_1`.
- `lastRowMeasure n D = (D.measure.withDensity quotientDensity) ⊗ (volume ⊗ unitsHaar)`, where
  `quotientDensity n [g] = |det g|⁻¹` and `RealRankZero.unitsHaar` is the Haar measure
  `|u|⁻¹ du` on `ℝˣ`.

So `∫_(Q_(n+1)) f dD' = C ∫_(Q_n) ∫_(ℝ^(n+1)) ∫_(ℝˣ) f([[[g,0],[x,u]]]) |det g|⁻¹ |u|⁻¹ du dx dD([g])`.
`realLastRowChart` proves the statement. `lastRowChart_integral` gives the consequences used by
integrals: for measurable `f : Q_(n+1) → ℂ`, `f` is `D'`-integrable exactly when `f ∘ lastRowChart n`
is `lastRowMeasure n D`-integrable, and `∫ f dD' = C ∫ f ∘ lastRowChart n d(lastRowMeasure n D)`.
The proofs use only the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## Proof

**The open cell.** For an invertible real matrix `y` in the domain of the Library's trailing-minor
chart `RealBruhatTrailingChart.trailingChart` (all trailing principal minors nonzero), let
`x = (trailingChart m).symm y`; then `y = U(x) L(x)` with `U(x)` upper triangular and `L(x)` lower
unitriangular. `cellLower y = diag(x) L(x)` is lower triangular with diagonal `x_ii ≠ 0`, and
`cellUpper y = U(x) diag(x)⁻¹` is upper unitriangular, with `cellUpper y · cellLower y = y`
(`cellUpper_mul_cellLower`, `cellUpper_isUpperTriangular`, `cellUpper_diag`,
`cellLower_isLowerTriangular`). `cellLower` is continuous on the chart target
(`continuousOn_cellLower`). Every `b ∈ B⁻_m` lies in the chart target with `cellLower b = b`
(`lowerTriangular_mem_trailingDomain`): its coordinates are `diag(b) + (diag(b)⁻¹ b - 1)`.

For an open `O ⊆ G_m`, the image of `B⁻_m ∩ O` in `N_m \ G_m` is the image under the open
quotient map of the open set of `g` in the chart target with `cellLower g ∈ O`
(`isOpenMap_lowerTriangularQuotientMap`; openness of `Units.val '' O` is `isOpen_val_image`).
With continuity and the Library's injectivity `lowerTriangularQuotientMap_injective`, the coset map
`b ↦ [b]` is an open embedding (`isOpenEmbedding_lowerTriangularQuotientMap`).

**Conull range** (`range_compl_null`). The cosets with no lower triangular representative are the
image of the set of `g` that are not of the form `u b`, `u ∈ N`, `b ∈ B⁻`; the Library's
`haar_setOf_not_upperUnipotent_mul_lowerTriangular` shows that this set is Haar-null in `G_(n+1)`
(every neighbourhood of `0` in `ℝ` contains a nonzero number, `exists_mem_nhds_ne_zero`). Weil's
formula for nonnegative measurable functions,
`IsCompatible.lintegral_eq_lintegral_quotientAverageENNReal`, applied to the indicator of the
preimage, gives `μ_N(N) · D(S) = 0`, and `μ_N(N) ≠ 0`.

**Pullback to `B⁻`** (`comap_properties`). The pullback `D.measure.comap β` along the cell
`β : B⁻_(n+1) → Q_n` is right invariant (right translation of cosets restricts to right
multiplication on `B⁻`), finite on compacts, σ-finite and nonzero, and pushes forward to
`D.measure` because the range is conull.

**Weighted product** (`measurePreserving_mulRight`). In block coordinates
`B⁻_(n+1) × M_(1×(n+1)) × B⁻_1 ≃ B⁻_(n+2)`, `(b, x, h) ↦ [[b, 0], [x, h]]` (the Library's
`lowerTriangularBlockMap`), right multiplication by `(g, y, h₀)` acts by
`(b, x, h) ↦ (b g, x g + h y, h h₀)` (`lowerTriangularBlockMap_mul`). The measure
`ρ_a |det b|⁻¹ ⊗ dx ⊗ ρ` (`ρ_a` right invariant on `B⁻_(n+1)`, `ρ` right invariant on `B⁻_1`) is
preserved: right translation multiplies the density by `|det g|` (`map_lowerDensity_mulRight`),
`x ↦ x g` multiplies Lebesgue measure by `|det g|⁻¹` (`map_rowMeasure_mulRight`, from Mathlib's
`Real.map_matrix_volume_pi_eq_smul_volume_pi`), and the shear `x ↦ x + h y` preserves the product
by Fubini (`measurePreserving_shear`, `measurePreserving_diagonal`).

**Comparison** (`chart_eq_smul_map`). The pushforward of the weighted product to `B⁻_(n+2)` is
right invariant, finite on compacts and nonzero, as is the pullback of `D'`. The Library's
uniqueness `exists_pos_smul_eq_of_isMulRightInvariant` (module `LowerTriangularQuotientCellMeasure`)
gives a positive scalar. Pushing forward along the cell of rank `n + 2` and using
`|det g|⁻¹ ∘ β = |det b|⁻¹` (`quotientDensity_cell`, from `quotientDetAbs_mk`) yields
`D'.measure = ofReal C • map chart (D.measure |det|⁻¹ ⊗ dx ⊗ ρ)`.

**Coordinates `(x, u)`** (`exists_lastRowChart`). With `ρ = lowerHaar`, the pushforward of
`unitsHaar` along the homeomorphism `unitsLowerHomeomorph : ℝˣ ≃ₜ B⁻_1` (right invariant, finite on
compacts, σ-finite, nonzero), and `rowEquiv` measure preserving, the product measure is the
pushforward of `lastRowMeasure n D` (`map_prod_map`).

## Provenance

Internal. The lower-block coordinates `[[g, 0], [x, h]]` on `N \ GL` with measure
`|det g|^(-d) dg dx d_r h` are those of H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika,
*Rankin–Selberg convolutions*, Amer. J. Math. 105 (1983), §9.3, printed pp. 456–457, where the change
of variables is stated up to a positive constant over a p-adic field. The module is the real
counterpart, with one appended row (`d = 1`), of the Library's p-adic comparison
`lowerBlockQuotient_eq_smul_map_chart` (module `LowerBlockQuotientMeasureComparison`), whose
argument it follows; the real open cell and conullness are proved here by the trailing-minor chart
and Weil's formula. The last-row coordinates `(x, h)` are those of H. Jacquet, *Archimedean
Rankin–Selberg integrals* (2009), §6.2, Propositions 6.1–6.2, pp. 41–42 of the author-posted
version, where the restriction of a Whittaker function to the matrices `[[g, 0], [x, h]]` is
multiplied by a function `φ(x, h)` of the last row, using right translates by upper column
unipotent elements.
