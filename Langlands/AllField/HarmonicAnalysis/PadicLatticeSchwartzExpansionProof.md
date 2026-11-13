# All-field port of `Langlands.HarmonicAnalysis.PadicLatticeSchwartzExpansionProof`

`Langlands.AllField.HarmonicAnalysis.PadicLatticeSchwartzExpansionProof` is the all-field port of the Library module `Langlands.HarmonicAnalysis.PadicLatticeSchwartzExpansionProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

Source: the original module `Langlands.HarmonicAnalysis.PadicLatticeSchwartzExpansionProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Single-lattice coset expansions of local-field Schwartz–Bruhat functions**

Local constancy and compactness of the support give one valuation lattice under
whose translations a test function is invariant. Finitely many cosets of that
lattice cover the support, and their distinct classes in the quotient give the
expansion with sampled coefficients. See the paired Markdown for the route.

## Imports from the port

- `Langlands.AllField.HarmonicAnalysis.PadicLatticeGeometryProof`
- `Langlands.AllField.HarmonicAnalysis.PadicLatticeSchwartzExpansionStatement`

## Declarations

- `Langlands.AllField.HarmonicAnalysis.padicSchwartzBruhat_exists_additiveLattice_invariant` (theorem): Every Schwartz–Bruhat function on a supplied nonarchimedean local field is invariant under
  the translations by one valuation lattice `T.additiveLattice m`. The level is
  derived from local constancy and compact support in the supplied topology.
- `Langlands.AllField.HarmonicAnalysis.padicLatticeSchwartzExpansion` (theorem): Every Schwartz–Bruhat function on a supplied nonarchimedean local field is, at every point,
  a finite linear combination of indicators of cosets of one valuation lattice.
