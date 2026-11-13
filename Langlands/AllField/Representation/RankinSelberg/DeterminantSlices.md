# All-field port of `Langlands.Representation.RankinSelberg.DeterminantSlices`

`Langlands.AllField.Representation.RankinSelberg.DeterminantSlices` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.DeterminantSlices`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.DeterminantSlices` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Determinant slices and equal-rank slice coefficients**

JPSS (1983), Section 4.2, (4.2.1): the determinant fibers `|det g| = q^(-m)` of
the actual quotient `N_(n+1) \ GL_(n+1)` and the restricted integrals over them.
The measure is supplied. No convergence, support bound, compactness, or series
expansion of the full integral is asserted.

## Imports from the port

- `Langlands.AllField.Group.GL.UnramifiedCharacter`
- `Langlands.AllField.Representation.RankinSelberg.AnalyticStatement`

## Declarations

- `Langlands.AllField.RankinSelberg.continuous_ord_units` (theorem): The normalized order is continuous from the field units into the discrete integers.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.determinant_unipotent_mul`, `Langlands.RankinSelberg.determinantWeight_zero`, `Langlands.RankinSelberg.equalRankIntegrand_zero_mk`, `Langlands.RankinSelberg.determinantOrder`, `Langlands.RankinSelberg.determinantOrder_mk`, `Langlands.RankinSelberg.determinantSlice`, `Langlands.RankinSelberg.mem_determinantSlice`, `Langlands.RankinSelberg.mk_mem_determinantSlice`, `Langlands.RankinSelberg.mk_mem_determinantSlice_iff_normalizedAbs`, `Langlands.RankinSelberg.continuous_determinantOrder`, `Langlands.RankinSelberg.isClopen_determinantSlice`, `Langlands.RankinSelberg.isOpen_determinantSlice`, `Langlands.RankinSelberg.isClosed_determinantSlice`, `Langlands.RankinSelberg.measurableSet_determinantSlice`, `Langlands.RankinSelberg.disjoint_determinantSlice`, `Langlands.RankinSelberg.pairwise_disjoint_determinantSlice`, `Langlands.RankinSelberg.iUnion_determinantSlice`, `Langlands.RankinSelberg.determinantOrder_rightTranslate`, `Langlands.RankinSelberg.rightTranslate_mem_determinantSlice`, `Langlands.RankinSelberg.sliceCoefficient`, `Langlands.RankinSelberg.sliceCoefficient_def`, `Langlands.RankinSelberg.SliceIntegrableAt`, `Langlands.RankinSelberg.sliceIntegrableAt_iff`, `Langlands.RankinSelberg.SliceIntegrable`, `Langlands.RankinSelberg.SliceIntegrableAt.add`, `Langlands.RankinSelberg.SliceIntegrableAt.smul`, `Langlands.RankinSelberg.SliceIntegrable.add`, `Langlands.RankinSelberg.SliceIntegrable.smul`, `Langlands.RankinSelberg.sliceIntegrable_of_integrable`, `Langlands.RankinSelberg.sliceCoefficient_add`, `Langlands.RankinSelberg.sliceCoefficient_smul`, `Langlands.RankinSelberg.sliceCoefficient_add_fun`, `Langlands.RankinSelberg.sliceCoefficient_smul_fun`, `Langlands.RankinSelberg.sliceCoefficient_eq_integral_indicator`, `Langlands.RankinSelberg.equalRankSliceCoefficient`, `Langlands.RankinSelberg.equalRankSliceCoefficient_def`, `Langlands.RankinSelberg.equalRankIntegrand_eq_mul_spectralPoint_zpow`, `Langlands.RankinSelberg.setIntegral_equalRankIntegrand_determinantSlice`, `Langlands.RankinSelberg.sliceIntegrableAt_equalRankIntegrand_iff`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation.
