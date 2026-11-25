# ℚ_p is a nonarchimedean local field

Module `Nyll.ValuedFieldTheory.LocalField.Padic.NonarchimedeanLocalField`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file shows that Mathlib's field `ℚ_[p]`, with its norm topology and its valuative relation, is an instance of the class `IsNonarchimedeanLocalField` used by the library, which asks for a valuative topology, local compactness and a nontrivial relation.

## Main results

- `mulValuation_le_one_iff_norm_le_one`: `Padic.mulValuation x ≤ 1` if and only if `‖x‖ ≤ 1`.
- `integer_mem_iff_norm_le_one`: the valuation ring of the valuative relation on `ℚ_[p]` is the set of elements of norm at most one.
- `normedFieldValuation_compatible_padic`: the valuation `x ↦ ‖x‖` with values in `ℝ≥0` is compatible with the valuative relation, by comparing, for nonzero `x`, `‖x‖ = p^(−val x)` with `exp(−val x)`; zero is treated separately.
- `padicIsValuativeTopology`: the norm topology of `ℚ_[p]` is the valuative topology.
- `padicIsNonarchimedeanLocalField`: the instance; local compactness and nontriviality come from Mathlib.

All results assume `p` prime (as a `Fact`).

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/Padic/NonarchimedeanLocalField.lean`: the Lean file is the source byte for byte (SHA-256 `bf30d6e426361c54a92b5bb7952433b6d4a4dd189e54d7981db09ffe05aaab17`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
