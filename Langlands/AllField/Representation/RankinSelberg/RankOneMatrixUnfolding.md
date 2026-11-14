# All-field port of `Langlands.Representation.RankinSelberg.RankOneMatrixUnfolding`

`Langlands.AllField.Representation.RankinSelberg.RankOneMatrixUnfolding` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.RankOneMatrixUnfolding`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.RankOneMatrixUnfolding` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Unfolding the matrix integral over the unipotent variable**

For a matrix test function `Φ` and a left `(N, θ)`-equivariant function `f` on
`GL_(n+1)`, the matrix integral `∫ Φ(y) f(y) |det y|^s dy` equals the integral over
`(g, (a, k))` of `J(D(g, a) k) f(D(g, a) k) |det|^s` against
`|det g|⁻ⁿ dg × ω(1, a) da × dk|_K`, where `J` is the unipotent transform of `Φ`.
The absolute version holds for every measurable `f`.

## Imports from the port

- `Langlands.AllField.Representation.GodementJacquet.Zeta`
- `Langlands.AllField.Representation.RankinSelberg.RankOneMatrixUnipotentIntegral`

## Declarations

- `Langlands.AllField.RankinSelberg.RankOneIwasawa.integralSet` (abbrev): The integral subgroup `GL_(n+1)(O)` as a set.
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.diagPoint` (def): The point `D(g, a) k = diag(det g / ∏ a, a) · k`.
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.outerMeasure` (def): The product measure `|det g|⁻ⁿ dg × ω(1, a) da × dk|_K` of the outer variables.
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.outerMeasure_sFinite` (instance).
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.unfoldedMeasure_eq` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.unfoldedPoint_eq` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.det_unipotent_mul` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.abv_det_eq_one` (theorem): The absolute value of the determinant of an integral matrix is one.
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.determinantWeight_diagPoint` (theorem).
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.ae_outerMeasure_mem` (theorem): Almost every outer parameter has integral `k`.
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.matrixIntegrand_unfoldedPoint` (theorem): The matrix integrand at an unfolded point, using left equivariance of `f`.
- `Langlands.AllField.RankinSelberg.RankOneIwasawa.integral_matrixIntegrand_unfold` (theorem): **Unfolding, integral form.** If the matrix integral converges absolutely, the
  unipotent variable can be integrated first.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.RankOneIwasawa.continuous_diagPoint`, `Langlands.RankinSelberg.RankOneIwasawa.measurable_determinantWeight`, `Langlands.RankinSelberg.RankOneIwasawa.lintegral_matrixIntegrand_unfold`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
