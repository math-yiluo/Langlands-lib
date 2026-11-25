# Fixed points of adically contracting additive maps

Module `Nyll.ValuedFieldTheory.Valuation.Topology.AdicContractingFixedPoint`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `R` be a commutative ring, complete and Hausdorff for the `I`-adic topology of an ideal `I`. The file solves the affine fixed-point equation `x = b + T x` for an additive map `T` that raises the `I`-adic filtration by one step.

- `IsAdicComplete.existsUnique_eq_add_of_maps_pow_succ`: if `T : R →+ R` maps `I ^ n` into `I ^ (n + 1)` for every `n`, then for each `b ∈ R` there is exactly one `x ∈ R` with `x = b + T x`.

The proof takes the successive approximations `x₀ = 0`, `xₙ₊₁ = b + T xₙ`, which form an `I`-adic Cauchy sequence since `xₙ − xₙ₊₁ ∈ I ^ n`; Mathlib's precompleteness (`IsPrecomplete.prec`) gives a limit, which is a fixed point by the Hausdorff property. Uniqueness: the difference of two fixed points lies in every `I ^ n`. The difference estimate, the fixed-point property of the limit and uniqueness are private helper lemmas.

The map `T` is only additive, not `R`-linear, and the hypothesis is the filtration condition for all `n`, including `n = 0` (so `T` maps `R` into `I`).

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/Topology/AdicContractingFixedPoint.lean`: the Lean file is the source byte for byte (SHA-256 `e9d2d9dbef87d3ef8c0bb98a2e53d6d81d1aa32aaf8cab1bc09182b3da7fcdb6`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
