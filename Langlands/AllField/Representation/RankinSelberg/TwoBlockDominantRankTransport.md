# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockDominantRankTransport`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantRankTransport` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockDominantRankTransport`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockDominantRankTransport` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Transport for the dominant-rank parent proof**

Internal assembly tools. The lower analytic gamma and L conclusions remain open.
This file only transports supplied certificates along the published actual
normalized induction equivalence, reversing the complete dependent block family.

## Imports from the port

- `Langlands.AllField.Representation.Induction.OppositeProductReversalProof`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockBaseCasesStatement`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockJacquetData`

## Declarations

- `Langlands.AllField.RankinSelberg.DominantRankTransport.lowerReversed` (abbrev): The lower representation with the complete dependent block family reversed.
- `Langlands.AllField.RankinSelberg.DominantRankTransport.lowerReversedToUpperEquiv` (theorem): Reverse sizes, carriers and representations in the lower induction, then
  use the actual normalized equivalence to recover the original upper product.
- `Langlands.AllField.RankinSelberg.DominantRankTransport.gammaConclusion` (theorem): Reindex supplied lower gamma certificates and transport the induced-pair
  certificate along the actual normalized representation equivalence.
- `Langlands.AllField.RankinSelberg.DominantRankTransport.lConclusion` (theorem): Transport supplied lower L-polynomial certificates without altering the
  direction of the polynomial divisibility or its witnesses.
- `Langlands.AllField.RankinSelberg.DominantRankTransport.LowerGammaDominantInput` (def): The missing Section 4 gamma conclusion for the actual lower induction.
  This proposition is an unproved conditional interface.
- `Langlands.AllField.RankinSelberg.DominantRankTransport.LowerLDominantInput` (def): The missing Section 4 L conclusion for the actual lower induction.
  The polynomial equation is in the same direction as the published target.
- `Langlands.AllField.RankinSelberg.DominantRankTransport.gammaDominant_of_lower` (theorem): The actual lower gamma conclusion would imply the exact published dominant
  target, with no common-universe restriction or extra representation premise.
- `Langlands.AllField.RankinSelberg.DominantRankTransport.lDominant_of_lower` (theorem): The actual lower L conclusion would imply the exact published dominant
  target, preserving its polynomial witnesses and independent universes.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.DominantRankTransport.reverseSum`, `Langlands.RankinSelberg.DominantRankTransport.block_lt_of_dominant`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
