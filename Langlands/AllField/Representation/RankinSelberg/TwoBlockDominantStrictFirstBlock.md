# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockDominantStrictFirstBlock`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantStrictFirstBlock` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockDominantStrictFirstBlock`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockDominantStrictFirstBlock` in the Library. Its Markdown file gives the literature provenance of each statement.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantEqualSecondBlock`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantFirstBlockLaurentIdentityStatement`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantStrictNumerators`

## Declarations

- `Langlands.AllField.RankinSelberg.DominantRankTransport.StrictFirstBlockFactorCertificate` (def): Retained complete first-block witnesses at a strictly dominant test rank.
- `Langlands.AllField.RankinSelberg.DominantRankTransport.StrictFirstBlockCoefficientLaw` (def): One retained epsilon monomial and normalized polynomial pair work for
  all complementary rows, sections and actual large-model coefficients.
- `Langlands.AllField.RankinSelberg.DominantRankTransport.exists_strictFirstBlockBound_forOrdinaryFunctional` (theorem): The independently owned closed first-block result supplies a common bound
  for any functional realizing the same actual ordinary Jacquet integral.
- `Langlands.AllField.RankinSelberg.DominantRankTransport.exists_strictFirstBlockCoefficientLaw` (theorem): A common bound supplies a nonzero ordinary functional and its strict
  first-block law, conditional on the independently owned analytic theorem.
