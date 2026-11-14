# All-field port of `Langlands.Representation.CuspidalSupport.CuspidalTensorProof`

`Langlands.AllField.Representation.CuspidalSupport.CuspidalTensorProof` is the all-field port of the Library module `Langlands.Representation.CuspidalSupport.CuspidalTensorProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.CuspidalSupport.CuspidalTensorProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**External tensors of supercuspidal block factors**

The external tensor product of supercuspidal factors on the blocks of a
standard Levi is irreducible, admissible, and has zero coinvariants for every
proper standard refinement of the Levi.

## Imports from the port

- `Langlands.AllField.Representation.CuspidalSupport.CuspidalTensorStatement`

## Declarations

- `Langlands.AllField.CuspidalSupport.glCuspidalTensor` (theorem): Proof of `GLCuspidalTensorStatement`.

Public declarations of the original that are not re-declared here: `Langlands.CuspidalSupport.conjugateUnipotent_one`, `Langlands.CuspidalSupport.exists_parabolic_ne_top`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
