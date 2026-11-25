# A stabilizer criterion for simple subfields

Module `Nyll.ValuedFieldTheory.Ramification.HilbertRamification.GaloisStabilizer`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

In a finite Galois extension `M/K`, the file proves a criterion for comparing simple subextensions through their stabilizers in the Galois group.

- `adjoin_le_adjoin_of_forall_fixed_imp_fixed`: let `M/K` be finite Galois and `a, b ∈ M`. If every `σ ∈ Gal(M/K)` with `σ b = b` also satisfies `σ a = a`, then `K(a) ⊆ K(b)`.

The proof writes `K(b)` as the fixed field of the subgroup fixing it (Galois correspondence, `IsGalois.fixedField_fixingSubgroup`); `a` is fixed by that subgroup, hence lies in `K(b)`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Ramification/HilbertRamification/GaloisStabilizer.lean`: the Lean file is the source byte for byte (SHA-256 `90eab6f262ae11cada15472eb00ea809541997bdbdbb6319eff77e46ac5699f1`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
