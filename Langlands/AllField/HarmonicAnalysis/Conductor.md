# All-field port of `Langlands.HarmonicAnalysis.Conductor`

`Langlands.AllField.HarmonicAnalysis.Conductor` is the all-field port of the Library module `Langlands.HarmonicAnalysis.Conductor`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the unequal-rank JPSS functional equation needs. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.HarmonicAnalysis.Conductor` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

Conductors from the actual discrete valuation of a nonarchimedean local field.

## Imports from the port

- `Langlands.AllField.LocalField.Foundation`

## Declarations

- `Langlands.LocalFieldData.mem_integers_iff_discreteValuation_le_one` (theorem): The discrete valuation has exactly the already specified integer ring.
- `Langlands.LocalFieldData.additiveLattice` (def): The additive lattice of elements of order at least `-n`.
  This is the fractional ideal convention `π^(-n) O`, so it increases with `n`.
- `Langlands.LocalFieldData.mem_additiveLattice` (theorem).
- `Langlands.LocalFieldData.additiveLattice_mono` (theorem).
- `Langlands.LocalFieldData.mem_additiveLattice_iff_div_mem_integers` (theorem): The valuation-lattice definition is precisely the fractional ideal
  `π^(-n) O`, using the actual chosen uniformizer and integer ring.
- `Langlands.LocalFieldData.mem_additiveLattice_zero` (theorem): At level zero the additive lattice is the actual integer ring.
- `Langlands.LocalFieldData.exists_additiveLattice_subset` (theorem): Every neighborhood of zero contains an actual valuation lattice.
- `Langlands.LocalFieldData.AdditiveTrivialAt` (def): The character is trivial on the full fractional ideal `π^(-n) O`.
- `Langlands.LocalFieldData.exists_additiveTrivialAt` (theorem): Continuity gives a lattice on which the additive character is trivial.
  The proof uses the fact that the right half-circle contains no nontrivial subgroup.
- `Langlands.LocalFieldData.additiveTrivialAt_bddAbove` (theorem): Nontriviality supplies an upper bound for all triviality levels.
- `Langlands.LocalFieldData.exists_additiveConductor` (theorem): The largest integer triviality level exists; it is not assumed as character data.
- `Langlands.LocalFieldData.additiveConductor` (def): Tate's integer `n(ψ)`, the largest `n` for which `ψ(π^(-n) O)=1`.
  Choice is made only from the proved existence theorem immediately above.
- `Langlands.LocalFieldData.additiveConductor_spec` (theorem).
- `Langlands.LocalFieldData.additiveTrivialAt_iff_le_conductor` (theorem).

Public declarations of the original that are not re-declared here: `Langlands.PadicField.TopologicalData.exists_nontrivial_at_conductor_succ`, `Langlands.PadicField.TopologicalData.principalUnits`, `Langlands.PadicField.TopologicalData.mem_principalUnits`, `Langlands.PadicField.TopologicalData.mem_principalUnits_iff_div_mem_integers`, `Langlands.PadicField.TopologicalData.mem_principalUnits_zero`, `Langlands.PadicField.TopologicalData.principalUnits_antitone`, `Langlands.PadicField.TopologicalData.exists_principalUnits_subset`, `Langlands.PadicField.TopologicalData.MultiplicativeTrivialAt`, `Langlands.PadicField.TopologicalData.exists_multiplicativeTrivialAt`, `Langlands.PadicField.TopologicalData.multiplicativeConductor`, `Langlands.PadicField.TopologicalData.multiplicativeConductor_spec`, `Langlands.PadicField.TopologicalData.multiplicativeTrivialAt_iff_conductor_le`, `Langlands.PadicField.TopologicalData.exists_nontrivial_below_multiplicativeConductor`, `Langlands.PadicField.TopologicalData.IsUnramifiedQuasicharacter`, `Langlands.PadicField.TopologicalData.multiplicativeConductor_eq_zero_iff`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the functional equation.
