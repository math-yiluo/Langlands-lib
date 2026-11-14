# All-field port of `Langlands.Representation.RankinSelberg.EqualRankSliceSupportProof`

`Langlands.AllField.Representation.RankinSelberg.EqualRankSliceSupportProof` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.EqualRankSliceSupportProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.EqualRankSliceSupportProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Proof of equal-rank determinant-slice lower support**

On every sufficiently negative determinant slice the equal-rank integrand vanishes
pointwise, so its Bochner integral is zero. The bound combines the published uniform
simple-root support of smooth Whittaker coefficients, the Iwasawa decomposition and
the compact support of the row test function. No convergence is used.

## Imports from the port

- `Langlands.AllField.HarmonicAnalysis.ConductorSupplement`
- `Langlands.AllField.Representation.RankinSelberg.EqualRankSliceSupportStatement`
- `Langlands.AllField.Representation.Whittaker.SmoothSimpleRootSupportProof`

## Declarations

- `Langlands.AllField.RankinSelberg.normalizedAbs_finsetSum_le` (theorem): Ultrametric bound for a finite sum of the normalized absolute value.
- `Langlands.AllField.RankinSelberg.exists_schwartzBruhat_row_bound` (theorem): A row Schwartz–Bruhat function vanishes outside a box `|x_j| ≤ C` for the
  normalized absolute value.
- `Langlands.AllField.RankinSelberg.normalizedAbs_determinant_le_of_simpleRoot` (theorem): Determinant bound at a nonvanishing point. If the adjacent diagonal ratios of the
  Iwasawa diagonal are bounded by `R` wherever `W` is nonzero, and the last row of `g`
  lies in the box `|x_j| ≤ C`, then `|det g| ≤ ∏_i R^(n-i) C`.
- `Langlands.AllField.RankinSelberg.equalRankSliceSupport` (theorem): JPSS (1983), Section 4.2, printed page 407: the equal-rank slice coefficients have
  support bounded below, for all data of the statement.
