# All-field port of `Langlands.Representation.RankinSelberg.EqualRankSliceExpansionProof`

`Langlands.AllField.Representation.RankinSelberg.EqualRankSliceExpansionProof` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.EqualRankSliceExpansionProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.EqualRankSliceExpansionProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Proof of the conditional equal-rank determinant-series expansion**

JPSS (1983), Section 4.2, (4.2.1)–(4.2.2), printed pages 406–407. For any measure on
the Borel structure of the actual quotient `N_(n+1) \ GL_(n+1)`, a globally integrable
function is the sum of its integrals over the determinant slices, and these slice
integrals are absolutely summable. Applied to the equal-rank integrand at a convergent
parameter, this gives slice integrability at zero and the absolutely summable expansion
`Ψ(s) = Σ_m Ψ^m (q^(-s))^m`.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.EqualRankSliceExpansionStatement`

## Declarations

- `Langlands.AllField.RankinSelberg.hasSum_setIntegral_determinantSlice` (theorem): The integral of a globally integrable function is the unordered sum, over all
  `m : ℤ`, of its integrals over the determinant slices.
- `Langlands.AllField.RankinSelberg.summable_norm_setIntegral_determinantSlice` (theorem): The norms of the slice integrals of a globally integrable function are summable.
- `Langlands.AllField.RankinSelberg.equalRankSliceExpansion` (theorem): JPSS (4.2.2) at a convergent parameter: global integrability of the equal-rank
  integrand at `s` gives slice integrability at zero, absolute summability of
  `a(m) (q^(-s))^m`, and its `HasSum` to the equal-rank integral at `s`.
