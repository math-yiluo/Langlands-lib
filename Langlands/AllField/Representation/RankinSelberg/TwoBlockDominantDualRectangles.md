# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockDominantDualRectangles`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantDualRectangles` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockDominantDualRectangles`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockDominantDualRectangles` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Signed exchange of the two dominant rectangles**

The coordinate map needed for the strictly dominant reversed-dual calculation
exchanges the rectangles and applies negative transpose with both indices reversed.
It preserves the exact product of every supplied additive Haar measure.
This module does not compare the large-group matrices or their scalar kernels.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantRectangleHaar`

## Declarations

- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.measurePreserving_dualRectangleEquiv` (theorem): The signed rectangle exchange preserves the exact supplied product Haar.
  No self-duality, nontrivial character, or positivity of `j,k` is required.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.integral_dualRectangleEquiv` (theorem): Total Bochner change of variables for the two actual rectangle products.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.TwoBlockDominantRectangular.signedReverseTranspose`, `Langlands.RankinSelberg.TwoBlockDominantRectangular.signedReverseTranspose_apply`, `Langlands.RankinSelberg.TwoBlockDominantRectangular.signedReverseTranspose_symm_apply`, `Langlands.RankinSelberg.TwoBlockDominantRectangular.dualRectangleEquiv`, `Langlands.RankinSelberg.TwoBlockDominantRectangular.dualRectangleEquiv_apply`, `Langlands.RankinSelberg.TwoBlockDominantRectangular.dualRectangleEquiv_symm_apply`, `Langlands.RankinSelberg.TwoBlockDominantRectangular.continuous_signedReverseTranspose`, `Langlands.RankinSelberg.TwoBlockDominantRectangular.signedReverseTransposeHomeomorph`, `Langlands.RankinSelberg.TwoBlockDominantRectangular.dualRectangleHomeomorph`, `Langlands.RankinSelberg.TwoBlockDominantRectangular.measurable_signedReverseTranspose`, `Langlands.RankinSelberg.TwoBlockDominantRectangular.measurePreserving_signedReverseTranspose`, `Langlands.RankinSelberg.TwoBlockDominantRectangular.measurePreserving_dualRectangleEquiv_symm`, `Langlands.RankinSelberg.TwoBlockDominantRectangular.integrable_dualRectangleEquiv_iff`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
