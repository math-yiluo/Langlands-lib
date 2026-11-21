# Transfer from an irreducible Harris witness

`HarrisSupercuspidalIrreducibilityReductionStatement` is an internal
implication from one irreducible witness family for each eligible
cuspidal realization to `HarrisSupercuspidalRestrictionIrreducibleStatement`
in the same four independent universes. The premise supplies a genuine
pure compatible family, weakly associated to the class of the realization,
with the prescribed rank and absolutely irreducible restriction at each
coefficient place away from the residue characteristic of the split
supercuspidal place. The witness can have its own coefficient field,
complex embedding and pure weight.

The proof `harrisSupercuspidalRestrictionIrreducible_of_pureWitness`
chooses an actual spectral presentation from the supercuspidal component
hypothesis. It embeds the supplied coefficient completion into a \(p\)-adic
algebraic closure and extends the coefficient number field's complex
embedding to an identification of that closure with the complex field.
This selects a compatible completion of the witness coefficient field
over the same rational prime. Absolute irreducibility of the witness
restriction gives irreducibility over the common \(p\)-adic field.

The two families are weakly associated to the spectrum of the chosen
presentation. The proof applies `pureLocalIrreducibilityTransfer` at
their common positive rank, with both compatible coefficient embeddings,
to obtain absolute irreducibility of the supplied restriction. The last
step identifies the algebra structure induced by the canonical map to the
algebraic closure with its standard algebra structure, giving the exact
`scalarExtensionAlong` formulation.
