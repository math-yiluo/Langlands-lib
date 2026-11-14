# All-field port of `Langlands.Representation.RankinSelberg.IwasawaHaarIntegration`

`Langlands.AllField.Representation.RankinSelberg.IwasawaHaarIntegration` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.IwasawaHaarIntegration`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.IwasawaHaarIntegration` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Iwasawa integration on the whole group `GL_(n+1)`**

Haar measure on `GL_(n+1)(F)` is recovered from Borel coordinates
`(a, u) ↦ diag(a) u` and Haar measure restricted to `K = GL_(n+1)(O)`, by the
published factorization integral. Moving the diagonal factor to the right of the
unipotent factor introduces the inverse upper-Borel modulus.

## Imports from the port

- `Langlands.AllField.Group.GL.BlockModulusSupplement`
- `Langlands.AllField.Representation.RankinSelberg.DiagonalUnipotentHaar`
- `Langlands.AllField.Representation.RankinSelberg.IwasawaTorusPartitionProof`

## Declarations

- `Langlands.AllField.RankinSelberg.IwasawaHaar.integral_generalLinearHaar_iwasawa` (theorem): **Iwasawa integration on `GL_(n+1)(F)`**, Bochner form, with the
  normalizations of `generalLinearHaar_eq_map_iwasawa`:
  `∫_G f = ∫_K ∫_A δ(a)⁻¹ ∫_N f(u diag(a) k) du da dk` for integrable `f`.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.IwasawaHaar.borelPoint`, `Langlands.RankinSelberg.IwasawaHaar.shiftUnipotent`, `Langlands.RankinSelberg.IwasawaHaar.borelShift`, `Langlands.RankinSelberg.IwasawaHaar.borelPoint_shift`, `Langlands.RankinSelberg.IwasawaHaar.exists_borelPoint_mul`, `Langlands.RankinSelberg.IwasawaHaar.borelPoint_mem_iff`, `Langlands.RankinSelberg.IwasawaHaar.continuous_borelPoint`, `Langlands.RankinSelberg.IwasawaHaar.continuous_diagonalConj_prod`, `Langlands.RankinSelberg.IwasawaHaar.continuous_borelShift_snd`, `Langlands.RankinSelberg.IwasawaHaar.measurePreserving_borelShift`, `Langlands.RankinSelberg.IwasawaHaar.measure_borelPoint_preimage`, `Langlands.RankinSelberg.IwasawaHaar.measurable_of_map_diagonalConj`, `Langlands.RankinSelberg.IwasawaHaar.lintegral_borelPoint`, `Langlands.RankinSelberg.IwasawaHaar.lintegral_generalLinearHaar`, `Langlands.RankinSelberg.IwasawaHaar.iwasawaPoint`, `Langlands.RankinSelberg.IwasawaHaar.continuous_iwasawaPoint`, `Langlands.RankinSelberg.IwasawaHaar.lintegral_generalLinearHaar_prod`, `Langlands.RankinSelberg.IwasawaHaar.generalLinearHaar_eq_map`, `Langlands.RankinSelberg.IwasawaHaar.integral_generalLinearHaar`, `Langlands.RankinSelberg.IwasawaHaar.generalLinearHaar_eq_map_iwasawa`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
