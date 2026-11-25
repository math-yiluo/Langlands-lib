# Closed additive subgroups of ℤ_p

Module `Nyll.ValuedFieldTheory.LocalField.Padic.ClosedAddSubgroup`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file proves that a nonzero closed additive subgroup of the p-adic integers `ℤ_[p]` is open, and two small facts used with it.

## Main results

- `PadicInt.addSubgroup_isOpen_of_isClosed_of_ne_bot`: for a prime `p`, a closed additive subgroup `H ≠ 0` of `ℤ_[p]` is open. If `x ∈ H` is nonzero, closedness and density of ℤ in `ℤ_[p]` give `x·ℤ_[p] ⊆ H`; this ideal is `p^n ℤ_[p]`, a closed ball, which is open in an ultrametric space.
- `PadicInt.exists_positive_natCast_sub_mem_of_isOpen_addSubgroup`: every coset `z + H` of an open subgroup `H` contains a positive integer `n`, since the set `{n + 1 : n ∈ ℕ}` is dense in `ℤ_[p]`.
- `PadicInt.multiplicative_positiveNatDegree_ne_one`: in the multiplicative copy of `(ℤ_[p], +)`, the element `Multiplicative.ofAdd (1 : ℤ_[p])` raised to a positive natural power is not the identity, because `ℤ_[p]` has characteristic zero.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/Padic/ClosedAddSubgroup.lean`: the Lean file is the source byte for byte (SHA-256 `46a910b5fe03f3481386d6f677b3f1ab94b6851e310bf98fc322fadf4324522d`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
