# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockDominantFirstBlockLaurentIdentityStatement`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantFirstBlockLaurentIdentityStatement` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockDominantFirstBlockLaurentIdentityStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockDominantFirstBlockLaurentIdentityStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**The strictly dominant first-block JPSS Laurent identity**

JPSS (1983), Section 4.10(2), printed page 419, using the first-block calculation
of Section 4.9, printed pages 416–418. This closed proposition retains the
ordinary Jacquet realization, actual determinant-slice absolute integrability,
and common normalized-generator witnesses for a finite Laurent convolution
identity. It supplies no analytic proof or polynomial cancellation.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantQuotientKernelData`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockJacquetConvergenceStatement`
- `Langlands.AllField.Representation.RankinSelberg.UnequalRankDeterminantSlices`

## Declarations

- `Langlands.AllField.RankinSelberg.TwoBlockDominantFirstBlockLaurentIdentityStatement` (def): The first-block, polynomial-cleared identity for test rank `r + 1` strictly
  larger than induced rank `t + 1`. One real bound and one ordinary Jacquet
  functional work for every compatible quotient measure and every test. Actual
  slice convergence is unconditional in the small-block epsilon certificate;
  the certificate supplies common witnesses for the finite Laurent identity.
