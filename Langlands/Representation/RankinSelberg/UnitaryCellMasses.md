# Single-row cells of the mirabolic quotient and their masses

Author: Worker 1797. Module `Langlands.Representation.RankinSelberg.UnitaryCellMasses`,
namespace `Langlands.RankinSelberg.UnramifiedUnitary`.

This helper module serves the proof of
`Langlands.RankinSelberg.UnramifiedUnitaryPoleFreeStatement` (see
`UnramifiedUnitaryPoleFreeProof.md`). It specializes the cell bound of
`UnitaryCellBound` to the single-row torus elements `diag(ϖ^m, 1, …, 1)` of
`GL_(k+2)(F)`. It also computes a lower bound for their cell masses. All constructions are
internal. The mass is the classical inverse modulus `δ_B⁻¹`, as in the Iwasawa integration
formula on `N \ GL_(k+1)`.

## Single-row torus elements (section `Torus`)

- `singleRow k m : Fin (k+1) → ℤ` is the exponent `(m, 0, …, 0)`.
- `levi_torus`: the Levi embedding `Mirabolic.levi` sends `torus ϖ λ` (in `GL_(k+1)`) to
  `torus ϖ (Fin.snoc λ 0)` (in `GL_(k+2)`). This is an entrywise check with `levi_first`,
  `levi_last` and `levi_bottom`. `snoc_singleRow` identifies the extended exponent.
- `rowElement ϖ k m = levi (torus ϖ (singleRow k m))`, an element of the mirabolic group
  `P_(k+1) ⊆ GL_(k+2)`. `rowElement_val`: as a matrix it is `torus ϖ` of the exponent
  `i ↦ if i = 0 then m else 0`, i.e. `diag(ϖ^m, 1, …, 1)`.

## The torus lower bound (section `Masses`)

- `density_le_quotientMeasure`: let `Y ⊆ N \ GL_(k+1)` contain the classes of `ϖ^λ k` for
  every integral `k`. Then `δ(λ) ≤ μ(Y)`, where `μ` is the published
  `unipotentQuotientHaar F k` and `δ` is the published `QuotientTorusEnvelope.density`
  (the inverse modulus). Proof: rewrite `μ` with the published torus decomposition
  `QuotientTorusEnvelope.quotientMeasure_eq_sum_torus`, which writes it as the sum over `λ`
  of `δ(λ)` times the pushforward of the normalized Haar measure on `GL_(k+1)(O)` along
  `k ↦ [ϖ^λ k]`. Then keep only the `λ` term (`Measure.le_sum`), use
  `Measure.le_map_apply`, and use the fact that the pulled-back set contains `GL_(k+1)(O)`,
  which has mass one (`generalLinearHaar_integralSubgroup`). No measurability of `Y` is
  needed.
- `density_singleRow`: `δ(singleRow k m) = q^(k m)` for the canonical uniformizer. Only the
  pairs `(0, j)` with `j > 0` contribute, each with factor `|ϖ^m| = q^(-m)`
  (`uniformizerUnit_zpow_abs`).

## The measure on `N \ P` (section `MirabolicMeasure`)

The field carries its canonical topology, valuation and local-field structure.

- `mirabolicIntegral F k` is `GL_(k+2)(O) ∩ P`, the preimage of the published level-zero
  open subgroup. Its lemmas are `mem_mirabolicIntegral`, `isCompact_mirabolicIntegral`
  (`P` is closed) and `levi_mem_mirabolicIntegral` (`Iwasawa.rankInclusion_mem`).
- `exists_mirabolicMeasure F k`: there is a measure `ν` on `N \ P_(k+1)` that is finite on
  compacts, right invariant, and gives every compact-open orbit positive finite mass.
  Moreover `q^(k m) ≤ ν(orbit of t_m K t_m⁻¹)` for `t_m = rowElement ϖ k m` and
  `K = mirabolicIntegral F k`. The measure is the published `unipotentQuotientHaar F k`
  transported along the published homeomorphism
  `MirabolicQuotient.quotientHomeomorph : N \ P ≃ N_GL \ GL_(k+1)`. The first three
  properties are proved as in the published `MirabolicQuotient.exists_measure_succ`.
  For the mass: `ν(O) ≥ ν(R⁻¹ O)`, where `R` is right translation by `t_m⁻¹` (measure
  preserving). Then `ν(R⁻¹ O) ≥ μ(e⁻¹ R⁻¹ O)` (`le_map_apply`). For `x ∈ GL_(k+1)(O)`, the
  class of `ϖ^(singleRow) x` maps to the class of `t_m · levi x · t_m⁻¹`, which lies in the
  orbit since `levi x ∈ K`. `density_le_quotientMeasure` and `density_singleRow` then give
  `q^(k m)`.
- `rowElement_ne`: for `i ≠ j`, `t_i ∉ N t_j K`. If `t_i = h t_j κ`, the published Iwasawa
  uniqueness `Iwasawa.iwasawa_exponent_unique` in `GL_(k+2)` gives equal exponents, hence
  `i = j`.
- `rowSum_bounded`: let `ρ` be an irreducible admissible unitarizable representation of
  `GL_(k+2)(F)` with a nonzero standard Whittaker functional `ℓ`, and `v` a
  `GL_(k+2)(O)`-fixed vector. Then there is `C` with
  `∑_{m<M} q^(k m) |ℓ(ρ(diag(ϖ^m, 1, …, 1)) v)|² ≤ C` for all `M`. Proof: apply
  `padicCellBound` with the measure of `exists_mirabolicMeasure`, the subgroup
  `mirabolicIntegral F k` (which fixes `v`), and the distinct cells of `t_0, …, t_(M-1)`.
  Then compare termwise with the mass lower bound, using finiteness of the masses.
