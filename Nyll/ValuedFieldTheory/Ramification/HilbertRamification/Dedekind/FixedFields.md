# Decomposition and inertia fields of a prime

Module `Nyll.ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.FixedFields`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

A finite group `G` acts on a field `L` over `K` with `G` a Galois group of `L/K` (`IsGaloisGroup G K L`), and also on a ring `B`. For a prime ideal `P` of `B`, the file defines the decomposition field `Z_P` and inertia field `T_P` as the fixed fields in `L` of the decomposition group `G_P` and inertia group `I_P` from the Dedekind layer, and applies Mathlib's Galois correspondence to them.

## Main definitions and results

- `fixedFieldOfSubgroup G H`: the fixed field of a subgroup `H`. `fixedFieldOfSubgroup_fixingSubgroup_eq`: its fixing subgroup is `H`; the fixed field is `L` iff `H = 1`, and `K` iff `H = G`.
- `decompositionField G P`, `inertiaField G P`: `Z_P` and `T_P`, with membership lemmas.
- `dedekindDecomposition_decompositionField_fixingSubgroup_eq` and `dedekindRamification_inertiaField_fixingSubgroup_eq`: the subgroups fixing `Z_P` and `T_P` are `G_P` and `I_P`.
- `Z_P = L` iff `G_P = 1`, and `Z_P = K` iff `G_P = G`; when `G` is also a Galois group of `B` over `A` and `P` is prime over `p`, `Z_P = L` iff `p` has `|G|` primes above it, and `Z_P = K` iff it has exactly one.
- `T_P = L` iff `I_P = 1`, and `T_P = K` iff `I_P = G`.
- `dedekindTower_decompositionField_finrank_eq_decomposition_card`, `dedekindRamification_inertiaField_finrank_eq_inertia_card`: `[L : Z_P] = |G_P|` and `[L : T_P] = |I_P|`. The instances `decompositionGroup_isGaloisGroup` and `inertiaGroup_isGaloisGroup` make `G_P` and `I_P` Galois groups of `L/Z_P` and `L/T_P`.
- `decompositionField_le_inertiaField`: `Z_P ⊆ T_P`.

## Points to watch

- The actions of `G` on `B` and on `L` are separate data. The file does not assume that `B` lies in `L` or that the two actions agree; `Z_P` and `T_P` are defined through the subgroups `G_P` and `I_P` of `G` only.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Ramification/HilbertRamification/Dedekind/FixedFields.lean`: the Lean file is the source byte for byte (SHA-256 `4ce96ed5740819217c14feff06256ef617cd2a80c8a325839839abab5bff4e68`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
