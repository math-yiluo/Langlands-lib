# All-field supplement to `Langlands.AllField.Group.GL.NormalizedCharacter`

`Langlands.AllField.Group.GL.NormalizedCharacterSupplement` supplements the Library module `Langlands.AllField.Group.GL.NormalizedCharacter`, the existing all-field port of `Langlands.Group.GL.NormalizedCharacter`. The original belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The module imports the original, so the field-independent declarations of the original are available to it unchanged. This module re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use and that `Langlands.AllField.Group.GL.NormalizedCharacter` does not already provide. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders and the canonical data of the original (see the next paragraph) change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

The original uses the canonical topological data `F.canonicalTopologicalData` and the canonical normed-field structure `F.canonicalNormedField` of the p-adic field, and transports a supplied realization to it (`topology_eq_canonical…`). The port uses the supplied data `T : LocalFieldData F` throughout. Where the original quantifies over a p-adic field with its canonical data, the port quantifies over a field `F` and arbitrary data `T`. The transport is then unnecessary and is omitted.

Source: the original module `Langlands.Group.GL.NormalizedCharacter` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**The residue-normalized determinant character**

The value is the actual residue-cardinality-normalized absolute value of the
usual determinant. No unadjusted spectral norm is substituted.

## Imports from the port

- `Langlands.AllField.Group.GL.PadicSupplement`
- `Langlands.AllField.Representation.Whittaker.ParabolicInducedCoinvariantFinitenessProof`

## Declarations

- `Langlands.LocalFieldData.determinantNorm_eq_residue_pow` (theorem).
- `Langlands.LocalFieldData.continuous_normalizedAbsUnits` (theorem).
- `Langlands.LocalFieldData.determinantNormContinuous` (def): The normalized determinant is continuous for the actual matrix-unit topology.
- `Langlands.LocalFieldData.determinantNorm_eq_one_of_mem_compact` (theorem): The existing continuous positive-character theorem applies to the actual
  determinant norm on every compact matrix subgroup.

Declarations of the original re-declared by `Langlands.AllField.Group.GL.NormalizedCharacter` and therefore not here: `Langlands.PadicField.TopologicalData.normalizedAbsHom`, `Langlands.PadicField.TopologicalData.normalizedAbsHom_coe`, `Langlands.PadicField.TopologicalData.normalizedAbsUnits`, `Langlands.PadicField.TopologicalData.normalizedAbsUnits_coe`, `Langlands.PadicField.TopologicalData.determinantNorm`, `Langlands.PadicField.TopologicalData.determinantNorm_coe`, `Langlands.PadicField.TopologicalData.determinantNorm_scalar`, `Langlands.PadicField.TopologicalData.normalizedAbs_eq_one_iff_discreteValuation`, `Langlands.PadicField.TopologicalData.continuous_normalizedAbsHom`, `Langlands.PadicField.TopologicalData.isOpen_ker_normalizedAbsUnits`, `Langlands.PadicField.TopologicalData.isOpen_ker_determinantNorm`.

Public declarations of the original that are not re-declared here: `Langlands.PadicField.TopologicalData.determinantNorm_eq_canonicalNorm_pow_degree`, `Langlands.PadicField.canonicalDeterminantNorm`, `Langlands.PadicField.isOpen_ker_canonicalDeterminantNorm`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.

Not ported on purpose: `Langlands.PadicField.TopologicalData.normalizedAbsHom_eq`, `Langlands.PadicField.TopologicalData.determinantNorm_eq`. These are canonical-data wrappers, lemmas comparing two realizations of the same p-adic field, or facts that `Langlands.AllField.LocalField.Foundation` and `Langlands.LocalFactor.LocalAbelian` already provide for every local field; the port works with one supplied realization throughout.
