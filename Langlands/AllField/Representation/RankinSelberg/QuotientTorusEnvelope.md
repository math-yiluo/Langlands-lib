# All-field port of `Langlands.Representation.RankinSelberg.QuotientTorusEnvelope`

`Langlands.AllField.Representation.RankinSelberg.QuotientTorusEnvelope` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.QuotientTorusEnvelope`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.QuotientTorusEnvelope` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

Summable torus envelopes for the actual standard unipotent quotient.

## Imports from the port

- `Langlands.AllField.Group.GL.BlockModulusSupplement`
- `Langlands.AllField.Representation.RankinSelberg.QuotientIwasawaIntegrationProof`

## Declarations

- `Langlands.AllField.RankinSelberg.QuotientTorusEnvelope.density` (def): The literal inverse upper-Borel modulus on a uniformizer exponent vector.
- `Langlands.AllField.RankinSelberg.QuotientTorusEnvelope.density_pos` (theorem).
- `Langlands.AllField.RankinSelberg.QuotientTorusEnvelope.quotientMeasure_eq_sum_torus` (theorem): Every compatible quotient measure is the sum of the mass-one compact
  pushforwards with the exact inverse-modulus weights.
- `Langlands.AllField.RankinSelberg.QuotientTorusEnvelope.integrable_of_summable_torus_bound` (theorem): A measurable complex function with a summable torus envelope is absolutely
  integrable for every compatible standard quotient measure.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.QuotientTorusEnvelope.integrable_sum_smul_map_of_bound`, `Langlands.RankinSelberg.QuotientTorusEnvelope.sumPushforwardL1`, `Langlands.RankinSelberg.QuotientTorusEnvelope.sumPushforwardL1_coe`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
