# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockDominantQuotientKernelData`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantQuotientKernelData` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockDominantQuotientKernelData`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockDominantQuotientKernelData` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Actual dominant rectangle integrals on the lower quotient**

The simultaneous covariance of the raw kernel, followed by exact supplied-Haar
change of variables, gives complex, real norm-profile and Prop-valued descent.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantOuterIntegralData`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantRawKernel`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantRectangleHaar`

## Declarations

- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.representativeKernel` (def): Total integral of the actual weighted raw kernel over both supplied-Haar rectangles.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.representativeKernel_lowerBlockUnipotent_mul` (theorem): The rectangle integral, rather than the fixed-rectangle kernel, is left invariant.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.quotientKernel` (def): The actual complex quotient kernel, without choosing coset representatives.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.quotientKernel_mk` (theorem): Exact representative formula, valid also for nonintegrable inputs under the
  total Bochner convention.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.representativeNormProfile` (def): Integral of the norm of the raw kernel, retained as a total real integral.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.representativeNormProfile_lowerBlockUnipotent_mul` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.quotientNormProfile` (def): The real norm profile on the actual quotient. This is not the norm of
  `quotientKernel`.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.quotientNormProfile_mk` (theorem).
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.FiberIntegrable` (def): Actual integrability of the rectangle fiber. No convergence is asserted.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.fiberIntegrable_lowerBlockUnipotent_mul_iff` (theorem): Actual fiber integrability is invariant in both directions under left translation.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.quotientFiberIntegrable` (def): Prop-valued descent of actual fiber integrability, with no representative choice.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.KernelOuterIntegrable` (def): Actual outer integrability of the complex quotient kernel.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.KernelNormProfileIntegrable` (def): Actual outer integrability of the integral of the raw kernel's norm.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.KernelAbsoluteIntegrable` (def): Explicit absolute-input conditions for a prospective analytic successor.
  Fiber integrability remains a separate almost-everywhere requirement.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.kernelAbsoluteIntegrable_iff` (theorem): All three actual convergence conditions, stated separately and not asserted.
- `Langlands.AllField.RankinSelberg.TwoBlockDominantRectangular.kernelAbsoluteIntegrable_standard_iff` (theorem): The full absolute-input predicate in standard quotient coordinates.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.TwoBlockDominantRectangular.quotientFiberIntegrable_mk`, `Langlands.RankinSelberg.TwoBlockDominantRectangular.outerKernelIntegral`, `Langlands.RankinSelberg.TwoBlockDominantRectangular.outerKernelIntegral_eq`, `Langlands.RankinSelberg.TwoBlockDominantRectangular.outerKernelIntegral_standard`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
