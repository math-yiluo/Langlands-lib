# All-field port of `Langlands.Representation.Shahidi.IntertwiningCovariance`

`Langlands.AllField.Representation.Shahidi.IntertwiningCovariance` is the all-field port of the Library module `Langlands.Representation.Shahidi.IntertwiningCovariance`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

Source: the original module `Langlands.Representation.Shahidi.IntertwiningCovariance` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Parabolic covariance of Shahidi's intertwining integral**

If `f` transforms on the left under the standard `(m,n)` block parabolic by a
Levi scalar and a representation, the intertwining integral (0.1) of `f`
transforms under the `(n,m)` block parabolic, carried to total rank `m+n` by
`swapRank`, by the exchanged Levi data times the scaling factor of the change
of variables `a ↦ h₂⁻¹ a h₁`. Right invariance of `f` passes to the integral.

## Imports from the port

- `Langlands.AllField.HarmonicAnalysis.PadicRectangularHaarScalingProof`
- `Langlands.AllField.Representation.Shahidi.TwoBlocks`

## Declarations

- `Langlands.AllField.Shahidi.map_rectangularConj_padic` (theorem): Over a `p`-adic field, `a ↦ h₂⁻¹ a h₁` scales every Borel additive Haar measure
  on `n × m` matrices by `|det h₂|^m |det h₁|^(-n)`.

Public declarations of the original that are not re-declared here: `Langlands.Shahidi.twoBlockLeviSwap`, `Langlands.Shahidi.twoBlockLeviSwap_first`, `Langlands.Shahidi.twoBlockLeviSwap_second`, `Langlands.Shahidi.eq_upper_of_mem_unipotentSubgroup`, `Langlands.Shahidi.exists_upper_mul_blockSum`, `Langlands.Shahidi.measurable_mul_mul`, `Langlands.Shahidi.rectangularConj`, `Langlands.Shahidi.rectangularConj_apply`, `Langlands.Shahidi.hasIntegral_add_right`, `Langlands.Shahidi.HasIntertwiningIntegral.parabolic`, `Langlands.Shahidi.intertwiningOperator_parabolic`, `Langlands.Shahidi.intertwiningOperator_mul_right`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
