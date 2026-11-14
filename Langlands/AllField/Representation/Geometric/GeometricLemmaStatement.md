# All-field port of `Langlands.Representation.Geometric.GeometricLemmaStatement`

`Langlands.AllField.Representation.Geometric.GeometricLemmaStatement` is the all-field port of the Library module `Langlands.Representation.Geometric.GeometricLemmaStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

Source: the original module `Langlands.Representation.Geometric.GeometricLemmaStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

BZ77's normalized geometric lemma on actual smooth GL representations.

## Imports from the port

- `Langlands.AllField.Representation.Geometric.RefinementFunctorsSupplement`
- `Langlands.AllField.Representation.Induction.Parabolic`
- `Langlands.AllField.Representation.Jacquet.ParabolicSupplement`

## Declarations

- `Langlands.AllField.Geometric.geometricPieceFunctor` (def): The actual graded functor: normalized inner Jacquet, inverse-conjugation
  transport, then normalized inner induction. The equalities only relabel the
  same concrete subgroup; their existence is part of the theorem below.
- `Langlands.AllField.Geometric.jacquetInductionFunctor` (def): The actual composition whose natural filtration is asserted.
- `Langlands.AllField.Geometric.GeometricLemmaTheorem` (def): BZ77 2.12 together with its concrete standard-intersection identifications.
  Refinements, equalities, enumeration, filtration and natural graded
  isomorphisms are all conclusions, never theorem-valued parameters.
- `Langlands.AllField.Geometric.PadicGeometricLemmaTheorem` (def): The normalized geometric lemma for every pair of standard Levis in
  positive-rank GL over every actual finite p-adic extension.

Public declarations of the original that are not re-declared here: `Langlands.Geometric.subgroupEqualityFunctor`, `Langlands.Geometric.IsIntersectionRefinement`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
