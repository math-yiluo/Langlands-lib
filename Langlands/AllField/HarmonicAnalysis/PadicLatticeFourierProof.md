# All-field port of `Langlands.HarmonicAnalysis.PadicLatticeFourierProof`

`Langlands.AllField.HarmonicAnalysis.PadicLatticeFourierProof` is the all-field port of the Library module `Langlands.HarmonicAnalysis.PadicLatticeFourierProof`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`. Names are kept from the original, including `Padic` prefixes, although every declaration here applies to an arbitrary nonarchimedean local field.

Source: the original module `Langlands.HarmonicAnalysis.PadicLatticeFourierProof` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

**Plus-sign Fourier integrals of local-field lattice cosets**

A coset of a compact open additive subgroup has a convergent plus-sign Fourier
integrand. Translation invariance moves the coset to the subgroup, and
orthogonality on the subgroup leaves its mass or zero. For the valuation lattice
`π^(-m) O` the annihilator is `π^(-(n-m)) O`, by the conductor API.

## Imports from the port

- `Langlands.AllField.HarmonicAnalysis.PadicLatticeFourierStatement`
- `Langlands.AllField.HarmonicAnalysis.PadicLatticeGeometryProof`

## Declarations

- `Langlands.LocalFieldData.forall_mul_eq_one_iff_mem_additiveLattice` (theorem): The `ψ`-annihilator of `π^(-m) O` is `π^(-(n(ψ)-m)) O`.
- `Langlands.AllField.HarmonicAnalysis.padicLatticeFourier` (theorem): The published lattice-coset Fourier proposition, for every supplied topology.

Public declarations of the original that are not re-declared here: `Langlands.HarmonicAnalysis.coset_fourierIntegrand_integrable`, `Langlands.HarmonicAnalysis.coset_fourierIntegral_eq`, `Langlands.HarmonicAnalysis.subgroup_character_integral_of_trivial`, `Langlands.HarmonicAnalysis.subgroup_character_integral_of_nontrivial`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation.
