# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockDominantStrictGammaContinuation`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantStrictGammaContinuation` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockDominantStrictGammaContinuation`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockDominantStrictGammaContinuation` in the Library. Its Markdown file gives the literature provenance of each statement.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantEqualGammaContinuation`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantStrictGammaBound`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockDominantStrictLContinuation`

## Declarations

- `Langlands.AllField.RankinSelberg.DominantRankTransport.strictIntegral_central_translate` (theorem): The fixed central translation absorbs the model sign with the exponent
  of the larger rank in the actual strict integral.
- `Langlands.AllField.RankinSelberg.DominantRankTransport.StrictOppositeRealRayGammaCertificates` (def): Complete certificates for the fixed opposite spectral gamma product.
- `Langlands.AllField.RankinSelberg.DominantRankTransport.exists_strictOppositeRealRayGammaCertificates` (theorem): Unramified transport and complete-certificate uniqueness identify the
  large-real-twist witnesses with the two fixed original block factors.
- `Langlands.AllField.RankinSelberg.DominantRankTransport.strictTwoBlock_gamma_at_zero` (theorem): Continue the sign-absorbed strict gamma equations with the actual fixed
  right-Weyl first dual and swapped rectangular rows, then restore the sign.
- `Langlands.AllField.RankinSelberg.DominantRankTransport.strictTwoBlockSymmetricGammaProduct_at_zero` (theorem): The actual opposite-twist equations identify the complete gamma factor
  of the original strict-rank lower induction with the two original block factors.
