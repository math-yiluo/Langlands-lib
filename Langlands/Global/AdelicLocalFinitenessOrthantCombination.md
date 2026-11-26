# From orthant estimates to the Siegel weight

Module `Langlands.Global.AdelicLocalFinitenessOrthantCombination` (namespace
`Langlands.Global.StandardConstantTerm`). It works on any measurable space `X` with a measure `ν`,
a measurable coordinate map `c : X → (D → ℝ) × (Fin r → ℝ)` (root and central coordinates),
rates `ra`, `rb` with `rb ≥ 0`, thresholds `τ` and a predicate `J` on the root coordinates. The
orthant weights, heights and positive regions are those of
`Langlands.Global.AdelicLocalFinitenessChamberSlabs`.

## Definitions

- `siegelRegion τ = {x | x_β > τ_β for all β}`.
- `siegelWeight c ra rb τ g = exp(-2 localFinitenessLogWeight ra rb (c g))` on `c⁻¹(siegelRegion τ)`
  and zero elsewhere, where `localFinitenessLogWeight ra rb (x, y) = ∑_β ra_β x_β + ∑_j rb_j |y_j|`
  (module `AdelicLocalFinitenessChamberWeights`).
- `orthantPos c τ J ε = {g | orthantHeight c τ J ε k g > 0 for all directions k}`.
- `orthantOf y` is the orthant of a central point (`ε_j` true iff `y_j ≥ 0`);
  `orthantCoord_orthantOf`: `orthantCoord (orthantOf y) j (y_j) = |y_j|`.

## Results

- `siegelWeight_le_sum`: `siegelWeight ≤ ∑_ε 1_{orthantPos ε} · orthantWeight ε` pointwise. On
  the Siegel region, the orthant of the point gives a term equal to the Siegel weight.
- `orthantWeight_le_siegelWeight`: on `orthantPos ε`, `orthantWeight ε ≤ exp(4 ∑_j rb_j) ·
  siegelWeight`. There the root coordinates outside `J` exceed their thresholds, those in `J` do
  by the definition of the orthant weight, and `|y_j| ≤ ε_j y_j + 2` because `ε_j y_j > -1`.
- `eLpNorm_two_add_measure_le`, `eLpNorm_two_finset_sum_measure_le`: the `L²` seminorm for a
  (finite) sum of measures is at most the sum of the seminorms
  (`ENNReal.rpow_add_le_add_rpow` with exponent `1/2`); `memLp_two_finset_sum_measure`.
- Measurability: `measurable_siegelWeight`, `measurable_orthantWeight`,
  `measurableSet_orthantPos`.
- `withDensity_siegelWeight_le`: `ν.withDensity siegelWeight ≤
  ∑_ε (ν.withDensity (orthantWeight ε)).restrict (orthantPos ε)`.
- `restrict_withDensity_orthantWeight_le`: for measurable `S ⊆ orthantPos ε`,
  `(ν.withDensity (orthantWeight ε)).restrict S ≤ exp(4 ∑_j rb_j) • (ν.withDensity siegelWeight).restrict S`;
  `lpNorm_orthant_le` gives the corresponding bound with factor `exp(2 ∑_j rb_j)` for `L²` norms.
- `siegel_estimate_of_orthants`: suppose that for every orthant `ε` the slab estimate holds for
  the orthant weight: square integrability of `φ` on a box `box ε ⊆ orthantPos ε` and of the
  residuals `res ε k` on `orthantPos ε` imply square integrability of `φ` on `orthantPos ε` with
  norm at most `C ε (‖φ‖_box + ∑_k ‖res ε k‖_pos)` (`C ε ≥ 0`). If `φ` is measurable and its boxes
  and residuals are square integrable for the Siegel weight, then `φ` is square integrable for
  the Siegel weight and
  `‖φ‖ ≤ exp(2 ∑_j rb_j) ∑_ε C ε (‖φ‖_{box ε} + ∑_k ‖res ε k‖_{orthantPos ε})`, all norms for the
  Siegel weight. Proof: transfer the hypotheses to the orthant weights by
  `restrict_withDensity_orthantWeight_le`, apply the orthant estimates, dominate the Siegel
  measure by the sum of the orthant measures and transfer back by `lpNorm_orthant_le`.

## Provenance

Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer. Math. Soc.
37 (2024), 187–234, §7.7, pp. 220–221 (literature id
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`). BL split `𝔞_G` into the orthants
spanned by `±H₀(z_j)`, take a weight `w_{λ_ε}` on each orthant and the direct sum of the
weighted spaces. The Library's Siegel weight (`localFinitenessLogWeight`, absolute central
terms) is the weight that agrees with the linear orthant weight on each closed orthant; this
module compares the two, with the positive regions `ε_j y_j > -1` slightly larger than the
closed orthants, at the cost of the factor `exp(4 ∑_j rb_j)`.
