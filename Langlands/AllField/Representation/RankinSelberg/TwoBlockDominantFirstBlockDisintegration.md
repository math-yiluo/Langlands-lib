# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockDominantFirstBlockDisintegration`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantFirstBlockDisintegration` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockDominantFirstBlockDisintegration`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockDominantFirstBlockDisintegration` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Joined row measures and the actual upper first-block coefficient**

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantFirstBlockIntegrands`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantUpperSliceAnalysis`

## Declarations

- `Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock.upperSliceConvergesAt` (theorem): Product convergence at a transported large rank, with no nonvanishing
  assumption on either supplied functional.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock.unequalRankSliceCoefficientAt_eq_integral` (theorem): Rank transport commutes with the actual iterated slice coefficient.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock.firstBlockUpperRowAverage` (def): The actual upper row integral evaluated at a representative of the
  small quotient. Its representative independence follows below.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock.firstBlockUpperRowAverage_eq` (theorem): The chosen representative disappears after the exact affine row
  substitution. The right side uses the actual small quotient integrand.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock.firstBlockUpperCoefficient` (def): The local upper first-block coefficient, retaining both actual
  rectangles and the supplied quotient slice.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock.firstBlockUpperCoefficient_eq_small` (theorem): Product convergence of the actual smaller integrand justifies the row
  disintegration; no convergence is deduced from total integral equalities.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlock.firstBlockUpperCoefficient_eq_small_of_whittakerType` (theorem): The actual local upper coefficient equals the actual smaller JPSS
  coefficient for the full Whittaker-type inputs, including zero functionals.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.TwoBlockDominantFirstBlock.firstBlockRowJoinEquiv`, `Langlands.RankinSelberg.TwoBlockDominantFirstBlock.firstBlockRowJoinEquiv_apply`, `Langlands.RankinSelberg.TwoBlockDominantFirstBlock.measurePreserving_firstBlockRowJoinEquiv`, `Langlands.RankinSelberg.TwoBlockDominantFirstBlock.integral_firstBlockJoinedRows`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
