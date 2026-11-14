# All-field supplement to `Langlands.AllField.Representation.RankinSelberg.ZeroRowLastRowCutoffProof`

`Langlands.AllField.Representation.RankinSelberg.ZeroRowLastRowCutoffProofSupplement` supplements the Library module `Langlands.AllField.Representation.RankinSelberg.ZeroRowLastRowCutoffProof`, the existing all-field port of `Langlands.Representation.RankinSelberg.ZeroRowLastRowCutoffProof`. The original belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The module imports the original, so the field-independent declarations of the original are available to it unchanged. This module re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use and that `Langlands.AllField.Representation.RankinSelberg.ZeroRowLastRowCutoffProof` does not already provide. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.ZeroRowLastRowCutoffProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Proof of the compact last-row cutoff for zero-row Whittaker coefficients**

An open stabilizer of a preimage vector contains small upper columns. Conjugating
them by `diag(g, I)` makes the Whittaker character read the last row of `g`, and
the additive conductor bounds that row. See the paired Markdown for the route.

## Imports from the port

- `Langlands.AllField.Group.GL.NormalizedCharacterSupplement`
- `Langlands.AllField.HarmonicAnalysis.ConductorSupplement`
- `Langlands.AllField.Representation.RankinSelberg.LastRowCompactOrbitProof`
- `Langlands.AllField.Representation.RankinSelberg.ZeroRowLastRowCutoffProof`
- `Langlands.AllField.Representation.RankinSelberg.ZeroRowLastRowCutoffStatement`

## Declarations

- `Langlands.AllField.RankinSelberg.zeroRowLastRowCutoff` (theorem): Every smooth zero-row Whittaker coefficient admits a zero-or-one compact
  open last-row cutoff, for every supplied p-adic field realization.

Declarations of the original re-declared by `Langlands.AllField.Representation.RankinSelberg.ZeroRowLastRowCutoffProof` and therefore not here: `Langlands.PadicField.TopologicalData.mem_additiveLattice_of_forall_mul_eq_one`.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.zeroRowColumnEntries`, `Langlands.RankinSelberg.zeroRowColumnEntries_mul`, `Langlands.RankinSelberg.zeroRowColumnEntries_zero`, `Langlands.RankinSelberg.zeroRowColumnEntries_eq_zero_of_le`, `Langlands.RankinSelberg.zeroRowColumnUnipotent`, `Langlands.RankinSelberg.zeroRowColumnUnipotent_val`, `Langlands.RankinSelberg.zeroRowColumnUnipotent_zero`, `Langlands.RankinSelberg.zeroRowColumnUnipotent_mem_upperUnipotent`, `Langlands.RankinSelberg.zeroRowColumnUnipotent_superdiagonal_sum`, `Langlands.RankinSelberg.standardCharacter_zeroRowColumnUnipotent`, `Langlands.RankinSelberg.appendIdentity_mul_zeroRowColumnEntries`, `Langlands.RankinSelberg.zeroRowColumnEntries_mul_appendIdentity`, `Langlands.RankinSelberg.appendIdentity_mul_zeroRowColumnUnipotent`, `Langlands.RankinSelberg.continuous_zeroRowColumnEntries`, `Langlands.RankinSelberg.continuous_zeroRowColumnUnipotent`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
