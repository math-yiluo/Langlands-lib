# All-field port of `Langlands.LocalFactor.Abelian.Definitions`

`Langlands.AllField.LocalFactor.Abelian.Definitions` is the all-field port of the Library module `Langlands.LocalFactor.Abelian.Definitions`, which belongs to the Library's development over p-adic fields `F : PadicField p` (with bundled topological data `F.TopologicalData` where a topology is needed). In the port, `F` is an arbitrary field with bundled data `T : LocalFieldData F` (a topology, a valuative relation and an `IsNonarchimedeanLocalField` structure, see `Langlands.LocalFieldData`). Nothing about the characteristic of `F` is assumed, so the port covers every nonarchimedean local field, including those of positive characteristic.

The port imports the original module, so the field-independent declarations of the original are available to it unchanged. It re-declares, under the same name with `Langlands.` replaced by `Langlands.AllField.` (declarations of the original namespace `Langlands.PadicField.TopologicalData` move to `Langlands.LocalFieldData`), the declarations that involve the field and that the Library's p-adic proofs of JPSS gamma-factor and L-factor multiplicativity (`Langlands.RankinSelberg.gammaMultiplicativity`, `Langlands.RankinSelberg.lFactorMultiplicativity`) use. Each re-declared declaration keeps the statement, and for a theorem the proof, of its original. Only the field binders change, and the `T`-API (residue cardinality, normalized absolute value, uniformizer and their lemmas) comes from `Langlands.LocalFieldData` and `Langlands.AllField.LocalField.Foundation`.

Source: the original module `Langlands.LocalFactor.Abelian.Definitions` in the Library. Its Markdown file gives the literature provenance of each statement.

## Contents

The module docstring of the port:

The actual abelian Gauss integral on a finite p-adic field.

## Imports from the port

- `Langlands.AllField.HarmonicAnalysis.ConductorSupplement`

## Declarations

- `Langlands.LocalFieldData.valuationShell` (def): The actual valuation shell of elements of order `-k`.
- `Langlands.LocalFieldData.valuationShell_compact_closed` (theorem): A nonzero valuation shell is compact in the supplied local-field topology.

Public declarations of the original that are not re-declared here: `Langlands.HarmonicAnalysis.Quasicharacter.extendZero`, `Langlands.HarmonicAnalysis.Quasicharacter.extendZero_zero`, `Langlands.HarmonicAnalysis.Quasicharacter.extendZero_unit`, `Langlands.HarmonicAnalysis.Quasicharacter.extendZero_ne_zero`, `Langlands.HarmonicAnalysis.Quasicharacter.continuousOn_extendZero`, `Langlands.HarmonicAnalysis.Quasicharacter.epsilonIntegrand`, `Langlands.HarmonicAnalysis.Quasicharacter.continuousOn_epsilonIntegrand`, `Langlands.PadicField.TopologicalData.valuationShell_ne_zero`, `Langlands.PadicField.TopologicalData.epsilonShell`, `Langlands.PadicField.TopologicalData.epsilonIntegrand_integrable`, `Langlands.PadicField.TopologicalData.abelianGaussIntegral`, `Langlands.PadicField.TopologicalData.abelianScale`, `Langlands.PadicField.TopologicalData.abelianScale_value`, `Langlands.PadicField.TopologicalData.abelianScale_order`, `Langlands.PadicField.TopologicalData.mem_valuationShell_iff_scaled_integral_unit`, `Langlands.PadicField.TopologicalData.abelianScale_abs_pos`, `Langlands.PadicField.TopologicalData.unramified_value_eq_of_value_eq`, `Langlands.PadicField.TopologicalData.normalizedAbs_unit_eq_of_value_eq`, `Langlands.PadicField.TopologicalData.integerVolume`, `Langlands.PadicField.TopologicalData.integerVolume_measure_ne_top`, `Langlands.PadicField.TopologicalData.abelianEpsilonExpression`, `Langlands.PadicField.TopologicalData.abelianEpsilonExpression_unramified`, `Langlands.PadicField.TopologicalData.abelianEpsilonExpression_ramified`, `Langlands.PadicField.TopologicalData.abelianEpsilonExpression_unramified_scale`. Each of them either does not involve the p-adic field, and is then available from the original module, or is not used by the two multiplicativity proofs.
