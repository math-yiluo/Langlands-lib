# All-field port of `Langlands.Representation.Whittaker.LeviCuspidalCoinvariantFinitenessProof`

`Langlands.AllField.Representation.Whittaker.LeviCuspidalCoinvariantFinitenessProof` is the all-field port of the Library module `Langlands.Representation.Whittaker.LeviCuspidalCoinvariantFinitenessProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). The original module does not name `PadicField` itself; the p-adic field enters through the statements that it proves or uses. In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.`, the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.Whittaker.LeviCuspidalCoinvariantFinitenessProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Finite twisted coinvariants of irreducible cuspidal Levi representations**

Factor the representation into irreducible supercuspidal block representations, restrict
the character to each block, and transport finite dimensionality of the tensor of the
blockwise coinvariants to the original quotient.

## Imports from the port

- `Langlands.AllField.Representation.CuspidalSupport.LeviTensorFactorizationProof`
- `Langlands.AllField.Representation.Whittaker.LeviCuspidalCoinvariantFinitenessStatement`
- `Langlands.AllField.Representation.Whittaker.SupercuspidalCoinvariantFinitenessProof`

## Declarations

- `Langlands.AllField.Whittaker.leviCuspidalCoinvariantFiniteness` (theorem): The finite-dimensionality part of the cuspidal-Levi coefficient step in
  Bernstein--Zelevinsky (1976), Theorem 7.12(5), for every locally constant character.
