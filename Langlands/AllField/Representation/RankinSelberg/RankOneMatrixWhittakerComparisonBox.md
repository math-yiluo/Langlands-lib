# All-field port of `Langlands.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonBox`

`Langlands.AllField.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonBox` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonBox`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonBox` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Every reduced rank-one value is a matrix–Whittaker value**

For `σ` smooth on `GL_(m+2)` over a p-adic field and a model function `W` of a
standard functional, the indicator `Φ₀` of an explicit compact open box of
matrices gives `Z(Φ₀, s + (m+1)/2, W) = C · Ψ(s, W)` with a constant `C > 0`
independent of `s`, whenever the `GL₁` integral
`Ψ(s, W) = ∫ W(diag(det g, 1, …, 1)) |det g|^(s - (m+1)/2) dg` converges
absolutely; the matrix integral then converges absolutely as well.

## Imports from the port

- `Langlands.AllField.LocalField.SmoothCharacterNormProofSupplement`
- `Langlands.AllField.Representation.GodementJacquet.Zeta`
- `Langlands.AllField.Representation.RankinSelberg.RankOneMatrixUnipotentIntegral`
- `Langlands.AllField.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonSupport`
- `Langlands.AllField.Representation.RankinSelberg.UnequalRankMirabolicUnitTestProof`
- `Langlands.AllField.Representation.Whittaker.MirabolicUnitTestProof`

## Declarations

- `Langlands.AllField.RankinSelberg.RankOneBox.boxEntry` (def): The entry sets of the box: `𝓛 A` at `(0,0)`, `𝓛 q` in the rest of row `0`, and
  `δᵢⱼ + 𝔪ᵃ` in the other rows.
- `Langlands.AllField.RankinSelberg.RankOneBox.box` (def): The compact open box of matrices.
- `Langlands.AllField.RankinSelberg.RankOneBox.mem_box_iff` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneBox.isOpen_boxEntry` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneBox.isCompact_boxEntry` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneBox.box_eq_pi` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneBox.isOpen_box` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneBox.isCompact_box` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneBox.one_mem_box` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneBox.integer_of_mem_principalLevel` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneBox.principalLevel_le_integral` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneBox.mul_mem_box` (theorem): Right multiplication by the principal level keeps the box, when the first row of
  the level is small enough.
- `Langlands.AllField.RankinSelberg.RankOneBox.mul_mem_box_iff` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneBox.exists_mem_principalLevel_mul_inv_upper` (theorem): An invertible matrix of the box is upper triangular after removing a principal
  level element on the right.
- `Langlands.AllField.RankinSelberg.RankOneBox.mul_sub_one_mem_levelSet` (theorem): Elements `x` with `x - 1 ∈ 𝔪ᵃ` form a group.
- `Langlands.AllField.RankinSelberg.RankOneBox.inv_sub_one_mem_levelSet` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneBox.unitLevel` (def): The units congruent to one modulo `𝔪ᵃ`, with their inverses.
- `Langlands.AllField.RankinSelberg.RankOneBox.mem_unitLevel_iff` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneBox.unitLevel_le_integralUnits` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneBox.diagonalUnits_mem_principalLevel` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneBox.torusBox` (def): The torus coordinates congruent to one modulo `𝔪ᵃ`.
- `Langlands.AllField.RankinSelberg.RankOneBox.torusFactor_mem` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneBox.unipotentBox` (def): The upper unipotent matrices whose first row is in `𝓛 q` off the corner and whose
  other rows are congruent to the identity modulo `𝔪ᵃ`.
- `Langlands.AllField.RankinSelberg.RankOneBox.standardCharacter_eq_one` (theorem): The standard character is trivial on the unipotent box.
- `Langlands.AllField.RankinSelberg.RankOneBox.unipotent_mul_rankOne_apply_zero` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneBox.unipotent_mul_rankOne_apply` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneBox.mem_box_unipotent_mul_iff` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneBox.point_eq_mul` (theorem): A parametrization point splits as `u · diag(det g, 1, …, 1) · diag((∏ t)⁻¹, t)`.
- `Langlands.AllField.RankinSelberg.RankOneBox.mem_torusBox_of_mem_box` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneBox.exists_point_mul_of_mem_box` (theorem): Every element of the integral group meeting the box on the left of a point is a
  point with integral torus coordinate times a principal level element.
- `Langlands.AllField.RankinSelberg.RankOneBox.measurePreserving_rshift` (theorem): Right translation by a point with integral torus coordinate preserves the parameter
  measure.
- `Langlands.AllField.RankinSelberg.RankOneBox.measurableSet_integralSubgroup` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneBox.lintegral_enorm_eq_of_support` (theorem): **Integration over the integral group, with a support set.** If on a measurable
  `S` every right translate by `k ∈ K` is a measure-preserving reparametrization and
  outside `S` the translate vanishes, the integral over `GL_(n+1)` is `dk(S)` times the
  parameter integral. Lebesgue version.
- `Langlands.AllField.RankinSelberg.RankOneBox.integral_eq_of_support` (theorem): Bochner version of `lintegral_enorm_eq_of_support`.
- `Langlands.AllField.RankinSelberg.RankOneBox.coe_unitLevel` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneBox.isOpen_unitLevel` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneBox.torusBox_eq_pi` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneBox.isOpen_torusBox` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneBox.unitLevel_measure_pos` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneBox.unitLevel_measure_le` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneBox.tailMeasure_torusBox` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneBox.tailMeasure_torusBox_pos` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneBox.tailMeasure_torusBox_lt_top` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneBox.continuous_unipotent_entry` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneBox.isOpen_unipotentBox` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneBox.one_mem_unipotentBox` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneBox.unipotentBox_subset` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneBox.unipotentHaar_unipotentBox_pos` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneBox.unipotentHaar_unipotentBox_lt_top` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneBox.boxSupport` (def): The integral elements `k` such that `point x₀ * k` lies in the box for some `x₀`.
- `Langlands.AllField.RankinSelberg.RankOneBox.isOpen_boxSupport` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneBox.one_mem_boxSupport` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneBox.restrict_boxSupport_pos` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneBox.restrict_boxSupport_lt_top` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneBox.continuous_determinantWeight` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneBox.continuous_glModelFunction` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneBox.rankOneEmbedding_eq_point` (theorem): The rank-one embedding is the parametrization point with trivial torus tail and
  unipotent coordinate.
- `Langlands.AllField.RankinSelberg.RankOneBox.continuous_rankOneEmbedding` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneBox.integral_param_of_eq` (theorem): The parameter integral of a function of product form. Bochner version.
- `Langlands.AllField.RankinSelberg.RankOneBox.lintegral_param_of_eq` (theorem): The parameter integral of a function of product form. Lebesgue version.
- `Langlands.AllField.RankinSelberg.RankOneBox.matrixIntegrand_mul_principalLevel` (theorem): The box integrand is right invariant under the principal level.
- `Langlands.AllField.RankinSelberg.RankOneBox.matrixIntegrand_point` (theorem): The box integrand at a parametrization point.
- `Langlands.AllField.RankinSelberg.RankOneBox.weight_smul_integrand` (theorem): The `GL₁` density turns the shifted exponent into the rank-one exponent.
- `Langlands.AllField.RankinSelberg.RankOneBox.exists_box_constant` (theorem): **The box computation.** For a smooth `σ` and a model function `W`, one compact
  open box `Φ₀` and one constant `C > 0` give `Z(Φ₀, s + (m+1)/2, W) = C · Ψ(s, W)`
  together with absolute convergence, whenever `Ψ(s, W)` converges absolutely.
- `Langlands.AllField.RankinSelberg.RankOneBox.rankOneModelValues_subset` (theorem): Every reduced rank-one value is a matrix–Whittaker value.
- `Langlands.AllField.RankinSelberg.rankOneModelValues_subset_whittakerRationalValues` (theorem): **Every reduced rank-one value is a matrix–Whittaker value.** For `σ` smooth on
  `GL_(m+2)` over a p-adic field and a standard functional `ℓ`, every rational function
  continuing an absolutely convergent `GL₁` integral
  `∫ W(diag(det g, 1, …, 1)) |det g|^(s - (m+1)/2) dg` of a model function `W` of `ℓ`
  is a shifted rational value of a matrix–Whittaker integral of the same model.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.RankOneBox.parameter_mul_comm`, `Langlands.RankinSelberg.RankOneBox.rshift`, `Langlands.RankinSelberg.RankOneBox.point_rshift`, `Langlands.RankinSelberg.RankOneBox.exists_point_eq`, `Langlands.RankinSelberg.RankOneBox.point_inv_isUpperTriangular`, `Langlands.RankinSelberg.RankOneBox.diagonalUnits_torusCoord`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
