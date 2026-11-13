# All-field port of `Langlands.Representation.RankinSelberg.UnequalRankMirabolicTowerFinite`

`Langlands.AllField.Representation.RankinSelberg.UnequalRankMirabolicTowerFinite` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.UnequalRankMirabolicTowerFinite`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.UnequalRankMirabolicTowerFinite` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Spectral finiteness of tower data**

Let `(ρ, q)` be a tower datum at level `i + 1` for a representation `η` of
`GL_(N+1)`. The upper unipotent radical of the block shape `(i + 1, N - i)` acts on
`q`-images through embedded radical elements of `P_(i+1)`. Hence `q` descends to a
map from the unnormalized Jacquet module of `η` for this shape to the quotient of
the carrier of `ρ` by its radical span. The block scalar `diag(a I_(i+1), I_(N-i))`
is the embedded element `leviScalar a`. If the block-scalar action on the Jacquet
module has finite-dimensional span, then `ρ (leviScalar a)` satisfies a nonzero
polynomial modulo the radical span.

## Imports from the port

- `Langlands.AllField.Representation.Parabolic.JacquetCenterSpanProof`
- `Langlands.AllField.Representation.RankinSelberg.UnequalRankBilinearUniquenessStatement`
- `Langlands.AllField.Representation.Smooth.SmallRealizationProof`
- `Langlands.AllField.Representation.Whittaker.MirabolicPairingStatement`

## Declarations

- `Langlands.AllField.RankinSelberg.UnequalRankTower.IsTower.exists_polynomial` (theorem): For an admissible irreducible `η`, the operator `ρ (leviScalar a)` of a tower datum
  at a positive level is annihilated modulo the radical span by a nonzero polynomial.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.UnequalRankTower.comp_aeval`, `Langlands.RankinSelberg.UnequalRankTower.towerShape`, `Langlands.RankinSelberg.UnequalRankTower.towerShape_index_val`, `Langlands.RankinSelberg.UnequalRankTower.towerShape_index_lt_iff`, `Langlands.RankinSelberg.UnequalRankTower.towerShape_unipotent_entry`, `Langlands.RankinSelberg.UnequalRankTower.towerShape_mem_upperUnipotent`, `Langlands.RankinSelberg.UnequalRankTower.towerShapeUnipotent`, `Langlands.RankinSelberg.UnequalRankTower.isLeading_towerShapeUnipotent`, `Langlands.RankinSelberg.UnequalRankTower.towerShape_blockScalar`, `Langlands.RankinSelberg.UnequalRankTower.standardCharacter_towerShapeUnipotent`, `Langlands.RankinSelberg.UnequalRankTower.IsTower.sub_mem_radicalSpan`, `Langlands.RankinSelberg.UnequalRankTower.IsTower.exists_polynomial_of_finiteDimensional`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation.
