# All-field port of `Langlands.Representation.CuspidalSupport.QuasicuspidalLeviAdmissibilityProof`

`Langlands.AllField.Representation.CuspidalSupport.QuasicuspidalLeviAdmissibilityProof` is the all-field port of the Library module `Langlands.Representation.CuspidalSupport.QuasicuspidalLeviAdmissibilityProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.CuspidalSupport.QuasicuspidalLeviAdmissibilityProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Admissibility of irreducible quasicuspidal product-Levi representations**

## Imports from the port

- `Langlands.AllField.Representation.CuspidalSupport.QuasicuspidalPrerequisitesStatement`
- `Langlands.AllField.Representation.Geometric.RefinementFunctors`
- `Langlands.AllField.Representation.Jacquet.Parabolic`

## Declarations

- `Langlands.AllField.CuspidalSupport.LeviAdmissibility.irreducibleQuasicuspidalLeviAdmissibility` (theorem): The published proposition family, from the published Cartan decomposition
  `Langlands.GeneralLinear.Cartan.cartanDecomposition` and Schur's lemma in countable
  dimension `Langlands.countableDimensionalSchur`.

Public declarations of the original that are not re-declared here: `Langlands.CuspidalSupport.LeviAdmissibility.exists_ne_zero_of_isIrreducible`, `Langlands.CuspidalSupport.LeviAdmissibility.span_orbit_eq_top`, `Langlands.CuspidalSupport.LeviAdmissibility.exists_finset_mul_inv_mem`, `Langlands.CuspidalSupport.LeviAdmissibility.rank_le_aleph0_of_doubleCoset_cover`, `Langlands.CuspidalSupport.LeviAdmissibility.exists_scalar_of_central`, `Langlands.CuspidalSupport.LeviAdmissibility.exists_levi_cartan`, `Langlands.CuspidalSupport.LeviAdmissibility.finite_fixedVectors`, `Langlands.CuspidalSupport.LeviAdmissibility.isAdmissible_of_isLeviQuasicuspidal`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation.
