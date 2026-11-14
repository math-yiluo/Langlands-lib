# All-field port of `Langlands.Representation.GodementJacquet.SupercuspidalCutoffFourierRegularity`

`Langlands.AllField.Representation.GodementJacquet.SupercuspidalCutoffFourierRegularity` is the all-field port of the Library module `Langlands.Representation.GodementJacquet.SupercuspidalCutoffFourierRegularity`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.GodementJacquet.SupercuspidalCutoffFourierRegularity` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Fourier regularity of actual supercuspidal coefficient cutoffs**

## Imports from the port

- `Langlands.AllField.HarmonicAnalysis.PadicLatticeGeometryProof`
- `Langlands.AllField.Representation.GodementJacquet.SupercuspidalCutoffFourier`
- `Langlands.AllField.Representation.RankinSelberg.EqualRankFrobeniusProof`
- `Langlands.AllField.Representation.RankinSelberg.ZeroRowLastRowCutoffProofSupplement`

## Declarations

- `Langlands.AllField.GodementJacquet.supercuspidalCutoffMatrixTest_fourier_singular` (theorem): The actual raw Fourier transform of every supercuspidal coefficient cutoff
  vanishes at every singular matrix, for the supplied additive Haar measure.
- `Langlands.AllField.GodementJacquet.supercuspidalCutoffMatrixTest_mem_fourierRegularMatrixTests` (theorem): With the supplied scalar self-dual measure, every actual coefficient cutoff
  belongs to the support-defined Fourier-regular matrix test space.

Public declarations of the original that are not re-declared here: `Langlands.GodementJacquet.exists_singular_inverseTranspose_stabilizer`, `Langlands.GodementJacquet.supercuspidalFourierRegularCutoff`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
