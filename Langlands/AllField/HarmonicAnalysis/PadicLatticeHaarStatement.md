# All-field port of `Langlands.HarmonicAnalysis.PadicLatticeHaarStatement`

`Langlands.AllField.HarmonicAnalysis.PadicLatticeHaarStatement` is the all-field port of the Library module `Langlands.HarmonicAnalysis.PadicLatticeHaarStatement`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

Source: the original module `Langlands.HarmonicAnalysis.PadicLatticeHaarStatement` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

Valuation-lattice Haar masses and a conductor-normalized Haar measure for each
supplied local-field topology, stated without any Fourier or self-duality hypothesis.

## Imports from the port

- `Langlands.AllField.HarmonicAnalysis.Conductor`

## Declarations

- `Langlands.AllField.HarmonicAnalysis.PadicLatticeHaarStatement` (def): For the supplied local-field topology, write `L m = π^(-m) O` for the valuation
  lattice `T.additiveLattice m` and `q` for the residue cardinality.

  * Every regular additive Haar measure gives each `L m`, for every integer `m`,
    a finite mass whose real value is positive and equals `q ^ m` times the
    real mass of `L 0 = O`.
  * For every continuous nontrivial unitary additive character `ψ` of conductor
    `n`, some regular additive Haar measure gives each `L m` the real mass
    `q ^ m / √(q ^ n)`, so the masses of `L m` and `L (n - m)` are reciprocal.

  Powers are integer powers, and no self-duality is asserted.
