# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockFirstBlockLaurentSections`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockFirstBlockLaurentSections` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockFirstBlockLaurentSections`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockFirstBlockLaurentSections` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**First-block coefficient functions of a two-block section**

For an actual lower-induced section `f` of `σ_0 ⊗ σ_1` and functionals `ℓ_0, ℓ_1`, the
scalar section at `diag(v, 1) g` is the inverse half modulus of `diag(v, 1)` times the
value at `v` of the actual coefficient function of `σ_0` of the vector obtained by
contracting the second tensor factor of `f(g)` with `ℓ_1`. Lower radical translates do
not change these coefficient functions.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerFirstBlockQuotientData`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockUnfoldingIntegrandData`

## Declarations

- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent.tensorContraction_blockTensor_blockPair_one` (theorem): Contraction against `ℓ_0 ⊗ ℓ_1` after acting by `diag(v, 1)` is `ℓ_0 (σ_0(v) y)`,
  where `y` is the contraction of the second factor.
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent.scalarSection_lowerRadical_mul` (theorem): The actual lower radical lies in the lower parabolic with trivial Levi projection,
  so it leaves every scalar section unchanged.
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent.firstBlockCoefficient` (def): The first-block coefficient function `v ↦ ℓ_0(σ_0(v) y)` of the contracted value
  `y = (1 ⊗ ℓ_1) f(g)`, as an element of the actual coefficient image of `σ_0`.
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent.firstBlockCoefficient_apply` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent.firstBlockCoefficient_lowerRadical_mul` (theorem): Lower radical translates have the same first-block coefficient function.
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent.scalarSection_firstBlockEmbedding_mul` (theorem): The scalar section at `diag(v, 1) g` is the inverse half modulus of `diag(v, 1)`
  times the first-block coefficient function at `v`.
- `Langlands.AllField.RankinSelberg.TwoBlockFirstBlockLaurent.inv_leviHalfModulus_blockPair_one` (theorem): The inverse half modulus of `diag(v, 1)` is the determinant weight `|det v|^(-b/2)`.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.TwoBlockFirstBlockLaurent.secondContraction`, `Langlands.RankinSelberg.TwoBlockFirstBlockLaurent.secondContraction_tprod`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
