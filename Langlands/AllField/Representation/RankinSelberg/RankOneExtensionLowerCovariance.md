# All-field port of `Langlands.Representation.RankinSelberg.RankOneExtensionLowerCovariance`

`Langlands.AllField.Representation.RankinSelberg.RankOneExtensionLowerCovariance` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.RankOneExtensionLowerCovariance`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.RankOneExtensionLowerCovariance` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Lower-parabolic covariance of the rank-one extension sections**

The lower block `B(m, x, a) = [m, 0; x, a]` lies in the opposite parabolic of the lower
shape `(t + 1, 1)`, with Levi part `(m, a)`. The scalar coefficient of an actual lower
induced section therefore satisfies
`c_f(B(m, x, a) g) = δ(m, a)^(-1/2) χ(a) · (ℓ ∘ σ(m) ⊗ id)(f(g))`, where
`δ(m, a) = |det m| / |a|^(t + 1)`.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.RankOneExtensionStableJacquetData`

## Declarations

- `Langlands.AllField.RankinSelberg.rankOneExtensionLowerShape_leviModulus` (theorem): The lower Levi modulus is `|det m| / |a| ^ (t + 1)`.
- `Langlands.AllField.RankinSelberg.rankOneExtensionLowerSectionCoefficient_lowerBlock_mul` (theorem): The coefficient formula
  `c_f(B(m, x, a) g) = δ(m, a)^(-1/2) χ(a) · (ℓ ∘ σ(m) ⊗ id)(f(g))`, with
  `δ(m, a) = |det m| / |a| ^ (t + 1)`.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.rankOneExtensionLowerLargeBlock`, `Langlands.RankinSelberg.rankOneExtensionLowerScalarBlock`, `Langlands.RankinSelberg.rankOneExtensionLowerShape_index_val`, `Langlands.RankinSelberg.rankOneExtensionLowerBlock_mem_oppositeParabolic`, `Langlands.RankinSelberg.rankOneExtensionLowerBlockParabolic`, `Langlands.RankinSelberg.rankOneExtensionLowerBlockParabolic_val`, `Langlands.RankinSelberg.oppositeLeviProjection_lowerBlock_large`, `Langlands.RankinSelberg.oppositeLeviProjection_lowerBlock_scalar_det`, `Langlands.RankinSelberg.piTensorProduct_comp_apply_eq_mul`, `Langlands.RankinSelberg.rankOneExtensionTensorContraction_tprod`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
