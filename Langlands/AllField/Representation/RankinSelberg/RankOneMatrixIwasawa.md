# All-field port of `Langlands.Representation.RankinSelberg.RankOneMatrixIwasawa`

`Langlands.AllField.Representation.RankinSelberg.RankOneMatrixIwasawa` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.RankOneMatrixIwasawa`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.RankOneMatrixIwasawa` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Iwasawa integration on `GL_(n+1)` with a rank-one torus coordinate**

The normalized Haar measure of `GL_(n+1)` over a canonical `p`-adic field is
recovered from its restriction to `K = GL_(n+1)(O)` and an explicit measure on
`(GL_1 × (Fˣ)ⁿ) × N`, where `N` is the upper unipotent group. A point
`((g, a), u)` maps to `u * diag(det g / ∏ a, a)`. The torus coordinate carries
the inverse modulus `δ⁻¹` as density; with the Library normalizations the
constant of the formula is exactly one.

## Imports from the port

- `Langlands.AllField.Group.GL.BlockModulusSupplement`
- `Langlands.AllField.Representation.RankinSelberg.DiagonalUnipotentHaar`
- `Langlands.AllField.Representation.RankinSelberg.IwasawaTorusPartitionProof`

## Declarations

- `Langlands.AllField.RankinSelberg.RankOneIwasawa.torusModulus` (def): The root modulus `δ(t) = ∏_{i<j} |t_i / t_j|` of the diagonal torus.
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.torusModulus_apply` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.continuous_torusModulus` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.torusModulus_eq_one` (theorem): The modulus is one on integral units.
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.continuous_det_units` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.continuous_torusCoord` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.weight` (def): The density `ω(b) = δ(D(b))⁻¹` on the parameter group `GL_1 × (Fˣ)ⁿ`.
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.weight_apply` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.continuous_weight` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.parameterMeasure` (def): The parameter measure: Haar measure on `GL_1 × (Fˣ)ⁿ` with density `ω`.
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.iwasawaMeasure` (def): The measure on the full parameter space `(GL_1 × (Fˣ)ⁿ) × N`.
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.parameterMeasure_sigmaFinite` (instance).
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.iwasawaMeasure_sFinite` (instance).
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.torusModulus_cons_one` (theorem): The modulus of `diag(x, 1, …, 1)` is `|x|ⁿ`.
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.weight_glOne` (theorem): The density on the `GL₁` factor alone is `|det g|⁻ⁿ`.
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.weight_split` (theorem): The density splits over the `GL₁` and torus factors.
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.det_point` (theorem): The determinant of a parametrization point is the determinant of its `GL₁`
  coordinate.
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.unipotentConj_map` (theorem): Diagonal conjugation scales the normalized unipotent Haar measure by `δ⁻¹`.
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.continuous_point` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.measurable_point` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.measurePreserving_shift` (theorem): Left translation in parameters preserves the parameter measure.
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.iwasawaMeasure_point_preimage` (theorem): The integral subgroup has preimage of mass one in the parameter space.
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.map_iwasawaMeasure_prod` (theorem): **Iwasawa integration with constant one.** Haar measure on `GL_(n+1)` is the
  pushforward of the parameter measure times Haar measure restricted to `GL_(n+1)(O)`
  under `(x, k) ↦ point x * k`.
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.glOneMeasure` (def): The measure `|det g|⁻ⁿ dg` on `GL₁`, the `GL₁` part of the density.
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.tailMeasure` (def): The measure `ω(1, a) da` on the torus tail `(Fˣ)ⁿ`.
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.glOneMeasure_sigmaFinite` (instance).
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.tailMeasure_sigmaFinite` (instance).
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.parameterMeasure_eq_prod` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.unfoldedMeasure` (def): The rearranged measure on `(GL₁ × ((Fˣ)ⁿ × GL_(n+1))) × N`: the unipotent variable
  is innermost and the `GL₁` variable outermost.
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.unfoldedPoint` (def): The point `u · diag(det g / ∏ a, a) · k` of the rearranged parameters.
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.measurable_unfoldedPoint` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.map_unfoldedMeasure` (theorem): **Unfolded Iwasawa integration.** Haar measure on `GL_(n+1)` is the pushforward of
  `(|det g|⁻ⁿ dg × ω(1, a) da × dk|_K) × du` under `((g, (a, k)), u) ↦ u D(g, a) k`.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.RankOneIwasawa.torusCoord`, `Langlands.RankinSelberg.RankOneIwasawa.torusCoord_zero`, `Langlands.RankinSelberg.RankOneIwasawa.torusCoord_succ`, `Langlands.RankinSelberg.RankOneIwasawa.torusSection`, `Langlands.RankinSelberg.RankOneIwasawa.det_diagonalUnits`, `Langlands.RankinSelberg.RankOneIwasawa.torusCoord_torusSection`, `Langlands.RankinSelberg.RankOneIwasawa.point`, `Langlands.RankinSelberg.RankOneIwasawa.continuous_diagonalUnits'`, `Langlands.RankinSelberg.RankOneIwasawa.shift`, `Langlands.RankinSelberg.RankOneIwasawa.point_shift`, `Langlands.RankinSelberg.RankOneIwasawa.det_glOne`, `Langlands.RankinSelberg.RankOneIwasawa.mem_integralSubgroup_zero_iff`, `Langlands.RankinSelberg.RankOneIwasawa.torusCoord_valuation_iff`, `Langlands.RankinSelberg.RankOneIwasawa.point_mem_integralSubgroup_iff`, `Langlands.RankinSelberg.RankOneIwasawa.exists_point_mul`, `Langlands.RankinSelberg.RankOneIwasawa.map_mul_left_withDensity`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
