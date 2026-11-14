# All-field supplement to `Langlands.AllField.HarmonicAnalysis.Conductor`

`Langlands.AllField.HarmonicAnalysis.ConductorSupplement` supplements the Library module `Langlands.AllField.HarmonicAnalysis.Conductor`, the existing all-field port of `Langlands.HarmonicAnalysis.Conductor`. The original belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The module imports the original, so the field-independent declarations of the original are available to it unchanged. This module re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use and that `Langlands.AllField.HarmonicAnalysis.Conductor` does not already provide. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.HarmonicAnalysis.Conductor` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

Conductors from the actual discrete valuation of a finite p-adic field.

## Imports from the port

- `Langlands.AllField.HarmonicAnalysis.Conductor`

## Declarations

- `Langlands.LocalFieldData.principalUnits` (def): The unit filtration, including `U⁰ = Oˣ`. For positive `n` the second
  condition is the usual congruence to one modulo the `n`th maximal-ideal power.
- `Langlands.LocalFieldData.mem_principalUnits` (theorem).
- `Langlands.LocalFieldData.mem_principalUnits_iff_div_mem_integers` (theorem): The congruence condition is measured against the actual fractional ideal
  `π^n O`; no arbitrary filtration is supplied as an input.
- `Langlands.LocalFieldData.principalUnits_antitone` (theorem).
- `Langlands.LocalFieldData.exists_principalUnits_subset` (theorem): The actual principal-unit groups are cofinal among neighborhoods of one.
- `Langlands.LocalFieldData.MultiplicativeTrivialAt` (def): Triviality of a quasicharacter on the actual `n`th unit subgroup.
- `Langlands.LocalFieldData.exists_multiplicativeTrivialAt` (theorem): Continuous complex quasicharacters are trivial at some principal-unit level.
  The no-small-subgroups input is the already proved complex power estimate.
- `Langlands.LocalFieldData.multiplicativeConductor` (def): Tate's conductor exponent `a(χ)`: the least unit-filtration level on which
  the quasicharacter is trivial, with zero precisely in the unramified case.
- `Langlands.LocalFieldData.multiplicativeConductor_spec` (theorem).
- `Langlands.LocalFieldData.multiplicativeTrivialAt_iff_conductor_le` (theorem).
- `Langlands.LocalFieldData.exists_nontrivial_below_multiplicativeConductor` (theorem): Every strictly lower unit level contains a nontrivial character value.

Declarations of the original re-declared by `Langlands.AllField.HarmonicAnalysis.Conductor` and therefore not here: `Langlands.PadicField.TopologicalData.mem_integers_iff_discreteValuation_le_one`, `Langlands.PadicField.TopologicalData.additiveLattice`, `Langlands.PadicField.TopologicalData.mem_additiveLattice`, `Langlands.PadicField.TopologicalData.additiveLattice_mono`, `Langlands.PadicField.TopologicalData.mem_additiveLattice_iff_div_mem_integers`, `Langlands.PadicField.TopologicalData.mem_additiveLattice_zero`, `Langlands.PadicField.TopologicalData.exists_additiveLattice_subset`, `Langlands.PadicField.TopologicalData.AdditiveTrivialAt`, `Langlands.PadicField.TopologicalData.exists_additiveTrivialAt`, `Langlands.PadicField.TopologicalData.additiveTrivialAt_bddAbove`, `Langlands.PadicField.TopologicalData.exists_additiveConductor`, `Langlands.PadicField.TopologicalData.additiveConductor`, `Langlands.PadicField.TopologicalData.additiveConductor_spec`, `Langlands.PadicField.TopologicalData.additiveTrivialAt_iff_le_conductor`.

Public declarations of the original that are not re-declared here: `Langlands.PadicField.TopologicalData.exists_nontrivial_at_conductor_succ`, `Langlands.PadicField.TopologicalData.mem_principalUnits_zero`, `Langlands.PadicField.TopologicalData.IsUnramifiedQuasicharacter`, `Langlands.PadicField.TopologicalData.multiplicativeConductor_eq_zero_iff`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
