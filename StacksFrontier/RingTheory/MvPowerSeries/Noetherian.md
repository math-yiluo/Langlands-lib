# Noetherianity of formal power series rings

Module `StacksFrontier.RingTheory.MvPowerSeries.Noetherian`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Formal power series in finitely many variables over a Noetherian commutative ring form a Noetherian ring.

`mvPowerSeries_fin_isNoetherianRing` proves this for `MvPowerSeries (Fin n) R` given `IsNoetherianRing R`. The private equivalences identify the zero-variable ring with its coefficient ring, reindex variables along a bijection, and identify series indexed by `Option σ` with one-variable series over `MvPowerSeries σ R` by splitting the exponent of the variable indexed by `none`.

The proof inducts on `n`. In the successor step, it reindexes `Fin (n + 1)` by `Option (Fin n)`, splits off one variable, and uses Noetherianity of univariate power series over the Noetherian ring supplied by induction.

The theorem is stated for `Fin n`. For another finite index type the result can be transported along a bijection with `Fin n`.

Stacks Project, Tag 0306.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [0306](https://stacks.math.columbia.edu/tag/0306) | `mvPowerSeries_fin_isNoetherianRing` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/MvPowerSeries/Noetherian.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
