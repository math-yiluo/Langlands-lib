# All-field port of `Langlands.Representation.RankinSelberg.LowerBlockQuotientMeasureComparison`

`Langlands.AllField.Representation.RankinSelberg.LowerBlockQuotientMeasureComparison` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.LowerBlockQuotientMeasureComparison`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.LowerBlockQuotientMeasureComparison` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Lower-block comparison of quotient measures**

A compatible quotient measure on `N_m \ GL_m` is the pushforward, along the open
cell `B⁻_m → N_m \ GL_m`, of its pullback to `B⁻_m`, which is right invariant and
finite on compacts. In block coordinates `B⁻_a × M_{d×a} × B⁻_d ≃ B⁻_{a+d}` the
determinant-weighted product of the pulled-back measure on `B⁻_a`, an additive
Haar measure on `M_{d×a}` and a right-invariant measure on `B⁻_d` is right
invariant on `B⁻_{a+d}`. Uniqueness of right-invariant measures then makes every
compatible quotient measure on `N_{a+d} \ GL_{a+d}` a positive multiple of the
lower-block chart pushforward of `D μ_a × dx × ρ`.

## Imports from the port

- `Langlands.AllField.Group.GL.LowerTriangularBigCellConull`
- `Langlands.AllField.Representation.RankinSelberg.LowerBlockWeightedProductInvariance`
- `Langlands.AllField.Representation.RankinSelberg.LowerTriangularQuotientCellMeasure`

## Declarations

- `Langlands.AllField.RankinSelberg.lowerTriangularQuotientMap_comap_of_isCompatible` (theorem): The pullback of a compatible quotient measure on `N_m \ GL_m` along the open
  cell `B⁻_m → N_m \ GL_m` is right invariant, finite on compacts, σ-finite and
  nonzero, and its pushforward along the cell is the quotient measure.
- `Langlands.AllField.RankinSelberg.lowerBlockQuotient_eq_smul_map_chart` (theorem): Lower-block comparison of quotient measures. Let `μa` and `μad` be compatible
  quotient measures on `N_a \ GL_a` and `N_{a+d} \ GL_{a+d}`, `η` an additive Haar
  measure on `F` and `ρ` a nonzero right-invariant measure on `B⁻_d`, σ-finite and
  finite on compacts. Then `μad = C • map chart ((μa.withDensity D).prod (dx.prod ρ))`
  for some real `C > 0`, where `chart ([g], x, h) = [[[g,0],[x,h]]]`,
  `D [g] = |det g|^(-d)` and `dx` is the rectangular Haar measure built from `η`.
