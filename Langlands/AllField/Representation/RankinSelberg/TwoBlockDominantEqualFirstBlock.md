# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockDominantEqualFirstBlock`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantEqualFirstBlock` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockDominantEqualFirstBlock`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockDominantEqualFirstBlock` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**First-block Laurent laws for actual equal-rank Jacquet coefficients**

The ordinary Jacquet realization and the published first-block theorem supply
the actual law at all sufficiently large real deformation parameters.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.EqualRankContinuedFormsProofSupplement`
- `Langlands.AllField.Representation.RankinSelberg.EqualRankFrobeniusProof`
- `Langlands.AllField.Representation.RankinSelberg.GammaFromWhittakerType`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantJacquetSeries`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockFirstBlockLaurentIdentityProof`
- `Langlands.AllField.Representation.RankinSelberg.UnequalRankFunctionalEquationProof`
- `Langlands.AllField.Representation.Whittaker.MirabolicCompactTwistedPairingProofSupplement`
- `Langlands.AllField.Representation.Whittaker.MirabolicPairingRigidityStepSupplement`

## Declarations

- `Langlands.AllField.RankinSelberg.DominantRankTransport.equalFirstBlockLowerSeries` (def): The actual lower quotient coefficient series of the equal-rank
  first-block unfolding, retaining both supplied measures.
- `Langlands.AllField.RankinSelberg.DominantRankTransport.EqualFirstBlockCoefficientLaw` (def): One epsilon monomial and one normalized polynomial pair, common to all
  sections, model coefficients and row tests, give the actual first-block law.
- `Langlands.AllField.RankinSelberg.DominantRankTransport.exists_equalFirstBlockCoefficientLaw` (theorem): Genuine ordinary Jacquet functionals and the actual first-block Laurent
  law exist above one bound, uniformly over both compatible quotient measures.
  The small-pair epsilon equation is derived from the published theorem.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.DominantRankTransport.firstBlock_lt_total`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
