# All-field port of `Langlands.Representation.RankinSelberg.UnramifiedTwistGammaProof`

`Langlands.AllField.Representation.RankinSelberg.UnramifiedTwistGammaProof` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.UnramifiedTwistGammaProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]` (see the next paragraph). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

Where the original quantifies over a p-adic field with its canonical data (`∀ (p : ℕ) [Fact p.Prime] (F : PadicField p)` together with `F.canonicalTopologicalData` or the canonical topology), the port quantifies over a field `F` with instances `[TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]`, and where the original uses the canonical data the port uses the data `(⟨⟩ : LocalFieldData F)` assembled from these instances (definitionally `LocalFieldData.ofInstances F`). Its topology is the ambient topology of `F`.

Source: the original module `Langlands.Representation.RankinSelberg.UnramifiedTwistGammaProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Complete symmetric unramified gamma spectral transport**

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.RankOneGammaTwistStatement`
- `Langlands.AllField.Representation.RankinSelberg.UnramifiedTwistGammaStatement`

## Declarations

- `Langlands.AllField.RankinSelberg.UnramifiedGammaTwist.padic_pair_both` (theorem): The canonical p-adic specialization keeps the field's actual residue
  cardinality, normalized absolute value, additive character and Haar measure.
- `Langlands.AllField.RankinSelberg.UnramifiedGammaTwist.padic_symmetric_both` (theorem): Reading the larger rank first covers either rank order and exchanges the
  two twist positions in the reversed branch.
- `Langlands.AllField.RankinSelberg.unramifiedTwistGamma` (theorem): Twisting either member by the supplied unramified determinant character
  transports the complete symmetric gamma certificate by `X ↦ q^(-u) * X`.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.UnramifiedGammaTwist.pair_factor`, `Langlands.RankinSelberg.UnramifiedGammaTwist.pair_both`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
