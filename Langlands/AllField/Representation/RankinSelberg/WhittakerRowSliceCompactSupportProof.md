# All-field port of `Langlands.Representation.RankinSelberg.WhittakerRowSliceCompactSupportProof`

`Langlands.AllField.Representation.RankinSelberg.WhittakerRowSliceCompactSupportProof` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.WhittakerRowSliceCompactSupportProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.WhittakerRowSliceCompactSupportProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Proof of compact support of Whittaker row data on a determinant slice**

JPSS (1983), Section 4.6, printed page 412: on each fixed determinant slice the
norm of `W(g) Φ(η g)` has compact support on `N_(n+1) \ GL_(n+1)`. At a point of
the support, the Iwasawa decomposition `g = u · diag(a) · κ`, the published uniform
simple-root bound and the row Schwartz–Bruhat bound bound every `|a_i|` above, and
the fixed determinant bounds every `|a_i|` below. The support therefore lies in the
image of a compact set of diagonal annuli times the integral subgroup, which is
compact in the Hausdorff quotient.

## Imports from the port

- `Langlands.AllField.HarmonicAnalysis.PadicLatticeTopology`
- `Langlands.AllField.Representation.RankinSelberg.EqualRankSliceSupportProof`
- `Langlands.AllField.Representation.RankinSelberg.IntegralDeterminant`
- `Langlands.AllField.Representation.RankinSelberg.WhittakerRowSliceCompactSupportStatement`

## Declarations

- `Langlands.AllField.RankinSelberg.exists_iwasawa_diagonal_le_of_simpleRoot` (theorem): Iwasawa diagonal bounds at a nonvanishing point. If the adjacent diagonal ratios
  are bounded by `R` wherever `W` is nonzero, and the last row of `g` lies in the box
  `|x_j| ≤ C`, then `g = u · diag(a) · κ` with `u` upper unipotent, `κ` integral and
  `|a_i| ≤ R^(n-i) C` for every diagonal entry.
- `Langlands.AllField.RankinSelberg.isCompact_normalizedAbs_annulus_units` (theorem): The units in a closed normalized-absolute-value annulus `c ≤ |a| ≤ M`, with
  `0 < c`, form a compact set in the topology of units.
- `Langlands.AllField.RankinSelberg.whittakerRowSliceCompactSupport` (theorem): JPSS (1983), Section 4.6, printed page 412: on each fixed determinant slice the
  norm of `W(g) Φ(η g)` has compact support on the actual quotient
  `N_(n+1) \ GL_(n+1)`, for every actual coefficient of every smooth representation.
