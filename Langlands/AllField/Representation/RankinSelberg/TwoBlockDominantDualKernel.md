# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockDominantDualKernel`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantDualKernel` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockDominantDualKernel`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockDominantDualKernel` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Actual dominant kernels under reversed duality**

The matrix comparison is an explicit premise. The section equivalence and
rectangle measures are the published actual constructions.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.AdjacentRankModelConvergenceProof`
- `Langlands.AllField.Representation.RankinSelberg.EqualRankContinuedFormsProofSupplement`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantDualRectangles`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantQuotientKernelData`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockDualSectionJacquetProof`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockLowerFourierGeometry`
- `Langlands.AllField.Representation.RankinSelberg.UnequalRankBilinearUniquenessStatement`

## Declarations

- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.reversedDualSectionEquiv` (def): An actual reversed-dual section equivalence chosen from the published
  Jacquet transport before all characters, functionals, tests and measures.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.reversedDualSectionEquiv_scalar` (theorem): Scalar realization for this fixed actual equivalence.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.rawKernel_reversedDual` (theorem): The actual unweighted kernels agree after signed exchange, with the
  prescribed right Weyl translation in the first dual test.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.kernel_reversedDual` (theorem): The actual weighted kernels agree at the complementary complex parameters.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.representativeKernel_reversedDual` (theorem): Exact supplied-Haar change of variables for the complex rectangle integral.
  This is an equality of total integrals and does not assert convergence.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.quotientKernel_reversedDual` (theorem): The complex identity descends along the actual published lower duality.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.TwoBlockDominantRectangular.representativeNormProfile_reversedDual`, `Langlands.RankinSelberg.TwoBlockDominantRectangular.fiberIntegrable_reversedDual_iff`, `Langlands.RankinSelberg.TwoBlockDominantRectangular.quotientNormProfile_reversedDual`, `Langlands.RankinSelberg.TwoBlockDominantRectangular.quotientFiberIntegrable_reversedDual_iff`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
