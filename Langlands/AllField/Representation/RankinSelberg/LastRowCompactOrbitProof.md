# All-field port of `Langlands.Representation.RankinSelberg.LastRowCompactOrbitProof`

`Langlands.AllField.Representation.RankinSelberg.LastRowCompactOrbitProof` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.LastRowCompactOrbitProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.LastRowCompactOrbitProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Proof of the exact compact open orbit of the last row**

The geometry is proved over any Hausdorff topological field and then applied to the
topology supplied by a p-adic field realization. See the paired Markdown for the route.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.LastRowCompactOrbitStatement`

## Declarations

- `Langlands.AllField.RankinSelberg.lastRowCompactOrbit` (theorem): The published last-row compact open orbit statement holds for every supplied
  p-adic field realization and every rank.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.mem_mirabolic_iff_lastRow`, `Langlands.RankinSelberg.lastRow_ne_zero`, `Langlands.RankinSelberg.lastRow_mem_image_iff`, `Langlands.RankinSelberg.continuous_lastRow`, `Langlands.RankinSelberg.isEmbedding_generalLinear_val`, `Langlands.RankinSelberg.isOpenEmbedding_generalLinear_val`, `Langlands.RankinSelberg.lastRow_image_mem_nhds`, `Langlands.RankinSelberg.isOpen_lastRow_image`, `Langlands.RankinSelberg.compactOpenIndicator`, `Langlands.RankinSelberg.coe_compactOpenIndicator`, `Langlands.RankinSelberg.lastRowCompactOrbit_of_field`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
