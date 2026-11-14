# All-field port of `Langlands.Representation.RankinSelberg.AdjacentRankJacquetNonzero`

`Langlands.AllField.Representation.RankinSelberg.AdjacentRankJacquetNonzero` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.AdjacentRankJacquetNonzero`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.AdjacentRankJacquetNonzero` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

Nonvanishing of the actual adjacent Jacquet functional by a compact local section.

## Imports from the port

- `Langlands.AllField.Group.GL.BlockIwahoriBasis`
- `Langlands.AllField.Representation.RankinSelberg.AdjacentRankJacquetCovariance`

## Declarations

- `Langlands.AllField.RankinSelberg.AdjacentJacquet.inducing_isSmooth` (theorem): The exact normalized tensor-valued inducing action is smooth.
- `Langlands.AllField.RankinSelberg.AdjacentJacquet.phase_eq_one_neighborhood` (theorem): The negative Jacquet phase is trivial on an open neighborhood of zero.
- `Langlands.AllField.RankinSelberg.AdjacentJacquet.exists_constantKernel_section` (theorem): A compact local section has the prescribed constant kernel near zero,
  with the phase killed on its full cell support.
- `Langlands.AllField.RankinSelberg.AdjacentJacquet.functional_ne_zero` (theorem): For any base character and supplied Haar, the actual Jacquet functional
  is nonzero whenever its all-section convergence premise holds.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.AdjacentJacquet.columnCoordinate`, `Langlands.RankinSelberg.AdjacentJacquet.columnCoordinate_upperColumn`, `Langlands.RankinSelberg.AdjacentJacquet.upperColumn_zero`, `Langlands.RankinSelberg.AdjacentJacquet.upperColumn_mem_radical`, `Langlands.RankinSelberg.AdjacentJacquet.eq_upperColumn_of_mem_radical`, `Langlands.RankinSelberg.AdjacentJacquet.continuous_columnCoordinate`, `Langlands.RankinSelberg.AdjacentJacquet.continuous_upperColumn`, `Langlands.RankinSelberg.AdjacentJacquet.nonzeroFunctional`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
