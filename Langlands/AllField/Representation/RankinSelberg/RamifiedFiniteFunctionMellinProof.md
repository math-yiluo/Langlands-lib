# All-field port of `Langlands.Representation.RankinSelberg.RamifiedFiniteFunctionMellinProof`

`Langlands.AllField.Representation.RankinSelberg.RamifiedFiniteFunctionMellinProof` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.RamifiedFiniteFunctionMellinProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.RamifiedFiniteFunctionMellinProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Uniform ramified Laurentness of scalar finite-function Mellin integrals**

Proof of `RamifiedFiniteFunctionMellinStatement`. A continuous finite function
on `Fˣ` is invariant under a principal-unit group `U^b`, chosen from the
finite function alone. For a quasicharacter nontrivial on `U^b`, the twisted
integrand vanishes below some order (compact support of the test), grows at
most geometrically along powers of the uniformizer (finite-function growth),
and is multiplied by a constant different from one under a unit translation
above some order (the test is constant near zero). The abstract shell theorem
then gives absolute convergence and a finite shell sum, which is a Laurent
polynomial in the spectral point.

## Imports from the port

- `Langlands.AllField.Representation.RankinSelberg.DeterminantSlicesSupplement`
- `Langlands.AllField.Representation.RankinSelberg.RamifiedFiniteFunctionMellinStatement`

## Declarations

- `Langlands.AllField.RankinSelberg.ramifiedFiniteFunctionMellin` (theorem): A continuous finite function on the units of a `p`-adic field has one
  principal-unit level beyond which every sufficiently ramified twist has
  convergent Mellin integrals with Laurent polynomial continuation.
