# All-field port of `Langlands.Representation.RankinSelberg.TwoBlockWhittakerDeformationProof`

`Langlands.AllField.Representation.RankinSelberg.TwoBlockWhittakerDeformationProof` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.TwoBlockWhittakerDeformationProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). The original module does not name `PadicField` itself; the p-adic field enters through the statements that it proves or uses. In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.TwoBlockWhittakerDeformationProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Proof of the entire Whittaker deformation for two lower-induced blocks**

Proof of `Langlands.AllField.RankinSelberg.TwoBlockWhittakerDeformationStatement`: the conditional
assembly `TwoBlockDeformation.twoBlockWhittakerDeformationStatement_of_normalizedProduct`
applied to the closed theorem `normalizedProductWhittakerType`.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.NormalizedProductWhittakerTypeProof`
- `Langlands.AllField.Representation.RankinSelberg.TwoBlockDeformationAssembly`

## Declarations

- `Langlands.AllField.RankinSelberg.twoBlockWhittakerDeformation` (theorem): JPSS 1983, Lemma of Section (4.5), printed pages 408-409, in its inverse-character
  form: every inverse-character Whittaker coefficient of `ρ₀` is the value at `0` of an entire
  family of such coefficients of `ρ_u` with one compact open right stabilizer.
