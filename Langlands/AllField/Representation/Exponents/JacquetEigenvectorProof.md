# All-field port of `Langlands.Representation.Exponents.JacquetEigenvectorProof`

`Langlands.AllField.Representation.Exponents.JacquetEigenvectorProof` is the all-field port of the Library module `Langlands.Representation.Exponents.JacquetEigenvectorProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.Exponents.JacquetEigenvectorProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Ordinary eigenvectors for generalized normalized Jacquet exponents**

A nonzero generalized-character vector of a commutative action, lying in a
finite-dimensional stable subspace, yields an ordinary eigenvector with the same
character. For the split centre of the normalized Jacquet module the stable
subspace is the space of vectors fixed by an open Levi subgroup, which is
finite-dimensional by normalized Jacquet admissibility.

## Imports from the port

- `Langlands.AllField.Representation.Parabolic.NormalizedJacquetAdmissibilityProof`

## Declarations

- `Langlands.AllField.Parabolic.twist_inverseHalfCharacter_leviCoinvariants_apply` (theorem): On every quotient class, the inverse-half twist of the product-Levi
  coinvariants acts as the normalized Jacquet action.
- `Langlands.AllField.Parabolic.twist_inverseHalfCharacter_leviCoinvariants` (theorem): The inverse-half twist of the product-Levi coinvariants is the normalized
  Jacquet representation.

Public declarations of the original that are not re-declared here: `Langlands.commute_sub_smul_one`, `Langlands.map_mem_characterSpace`, `Langlands.exists_mem_ker_of_pow_eq_zero`, `Langlands.exists_eigenvector_of_mem_characterSpace`, `Langlands.Parabolic.isAdmissible_normalizedJacquet`, `Langlands.Parabolic.splitCentreJacquet_mem_fixedVectors`, `Langlands.glJacquetExponentEigenvector`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation.
