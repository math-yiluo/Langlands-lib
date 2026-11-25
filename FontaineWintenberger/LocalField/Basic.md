# Local fields in the sense of Wintenberger

Module `FontaineWintenberger.LocalField.Basic`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

The file fixes the standing hypotheses of the library: a local field is a field complete for a discrete valuation, with perfect residue field of characteristic `p > 0`. The field is presented by its norm, as a `NontriviallyNormedField`.

## Definitions

- Notation `𝒪[K]` for the valuation ring `(NormedField.valuation K).valuationSubring` and `𝓀[K]` for its residue field, scoped to `FontaineWintenberger`.
- `IsCompleteDiscreteValuedField K`: `K` is ultrametric and complete, and `𝒪[K]` is a discrete valuation ring.
- `IsPerfectResidueLocalField K`: in addition `𝓀[K]` is perfect of prime characteristic.
- `residueChar K`: the residue characteristic `ringChar 𝓀[K]`, with an instance that it is prime; `residueChar_eq` identifies it with any characteristic `p` of `𝓀[K]`.
- `IsPerfectResidueLocalField.of_charP`: builds the class from the separate hypotheses.

## Points to watch

- These are the library's own classes. Unlike Mathlib's `IsNonarchimedeanLocalField`, the residue field need not be finite.
- The norm is used because Mathlib's spectral norm is stated for normed fields.

## References

Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, introduction.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/LocalField/Basic.lean` (SHA-256 of the source file `5c072b2fd618167b025a18aa19485361fd6aa0a0790090cb7d20d1184a833de1`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
