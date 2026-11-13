# All-field port of `Langlands.Representation.Geometric.WeylStatement`

`Langlands.AllField.Representation.Geometric.WeylStatement` is the all-field port of the Library module `Langlands.Representation.Geometric.WeylStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

Source: the original module `Langlands.Representation.Geometric.WeylStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

Concrete GL specializations of the Weyl and Bruhat prerequisites of BZ77.

## Imports from the port

- `Langlands.AllField.Group.GL.Padic`

## Declarations

- `Langlands.AllField.Geometric.PadicParabolicBruhatTheorem` (def): The actual inverse permutation matrices parametrize parabolic double
  cosets for every nonarchimedean local field.

Public declarations of the original that are not re-declared here: `Langlands.Geometric.WeylMinimalRepresentativeTheorem`, `Langlands.Geometric.PadicStandardIntersectionsTheorem`, `Langlands.Geometric.PadicGeometricWeylTheorems`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation.
