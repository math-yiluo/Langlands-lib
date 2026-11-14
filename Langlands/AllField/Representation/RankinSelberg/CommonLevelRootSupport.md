# All-field port of `Langlands.Representation.RankinSelberg.CommonLevelRootSupport`

`Langlands.AllField.Representation.RankinSelberg.CommonLevelRootSupport` is the all-field port of the Library module `Langlands.Representation.RankinSelberg.CommonLevelRootSupport`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.Representation.RankinSelberg.CommonLevelRootSupport` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Uniform simple-root bounds from a common right level**

## Imports from the port

- `Langlands.AllField.Group.GL.PadicSupplement`
- `Langlands.AllField.HarmonicAnalysis.ConductorSupplement`
- `Langlands.AllField.Representation.Whittaker.SmoothSimpleRootSupportProof`

## Declarations

- `Langlands.AllField.RankinSelberg.CommonLevel.exists_uniform_lattice` (theorem): A single small additive lattice works for all integral conjugates of every
  simple-root subgroup. Only openness of the supplied level is needed.
- `Langlands.AllField.RankinSelberg.CommonLevel.root_bound` (theorem): The common level bounds all adjacent diagonal ratios at every nonzero value,
  uniformly over the entire supplied family and the integral factor.

Public declarations of the original that are not re-declared here: `Langlands.RankinSelberg.CommonLevel.simpleRootUnipotent`, `Langlands.RankinSelberg.CommonLevel.simpleRootUnipotent_zero`, `Langlands.RankinSelberg.CommonLevel.simpleRootUnipotent_continuous`, `Langlands.RankinSelberg.CommonLevel.simpleRootUnipotent_character`, `Langlands.RankinSelberg.CommonLevel.diagonal_simpleRootUnipotent`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
