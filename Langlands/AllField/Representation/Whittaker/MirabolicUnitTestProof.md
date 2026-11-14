# All-field port of `Langlands.Representation.Whittaker.MirabolicUnitTestProof`

`Langlands.AllField.Representation.Whittaker.MirabolicUnitTestProof` is the all-field port of the Library module `Langlands.Representation.Whittaker.MirabolicUnitTestProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.Whittaker.MirabolicUnitTestProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Compact opposite-character mirabolic test functions: proof**

A compact open ambient subgroup is chosen inside the determinant-norm-one
locus and inside a neighborhood on which the standard character is trivial.
Its mirabolic intersection is the right stabilizer, and the character values
on the corresponding `N`-cosets are extended by zero.

## Imports from the port

- `Langlands.AllField.Representation.Whittaker.MirabolicUnitTestStatement`

## Declarations

- `Langlands.AllField.Whittaker.mirabolicUnitTest` (theorem): Compact opposite-character mirabolic test functions exist for every supplied
  p-adic realization, every unitary additive character and every rank.

Public declarations of the original that are not re-declared here: `Langlands.Whittaker.MirabolicUnitTest.cosetExtension`, `Langlands.Whittaker.MirabolicUnitTest.cosetExtension_mul`, `Langlands.Whittaker.MirabolicUnitTest.cosetExtension_eq_zero`, `Langlands.Whittaker.MirabolicUnitTest.cosetExtension_left`, `Langlands.Whittaker.MirabolicUnitTest.cosetExtension_right`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
