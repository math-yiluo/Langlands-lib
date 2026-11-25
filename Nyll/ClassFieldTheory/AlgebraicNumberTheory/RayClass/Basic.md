# Finite moduli and local congruence subgroups

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Basic`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a number field `K`, this file sets up the local data of ray congruence subgroups: finite moduli, the higher unit groups `U_v^(n)` at finite places, positivity at real places, and the corresponding subgroups of the finite and infinite ideles.

## Main definitions and results

- `RayClass.FiniteModulus K`: a finitely supported function from the finite places of `K` to `ℕ`, the exponents of the prime powers in a modulus.
- `RayClass.localHigherUnitMap v n`: reduction of the units of the valuation ring `O_v` of `K_v` to the units of `O_v / 𝔪_v^n`.
- `RayClass.localHigherUnitGroup v n`: the kernel of this map, as a subgroup of `K_vˣ`; this is `U_v^(n)`. `mem_localHigherUnitGroup_iff` unfolds membership, and `localHigherUnitGroup_zero` shows `U_v^(0)` is the whole group of units of `O_v`.
- `RayClass.infinitePositiveSubgroup v`: at a real place, the elements of `K_vˣ` that are positive under the real embedding of the completion; at a complex place the condition is empty and the subgroup is everything.
- `RayClass.finiteCongruenceSubgroup m`: the finite ideles `a` with `a_v ∈ U_v^(m(v))` for every finite place `v`; at places outside the support of `m` this asks that `a_v` be a unit of `O_v`.
- `RayClass.narrowInfiniteCongruenceSubgroup`: the infinite ideles positive at every real place.

## Points to watch

- `U_v^(n)` is defined as the kernel of reduction modulo `𝔪_v^n` on units. For `n ≥ 1` this is the usual `1 + 𝔪_v^n`, but the file does not state that description.
- A finite modulus carries no infinite part. The infinite subgroup here imposes positivity at every real place (the narrow condition), not at a chosen set of real places; moduli with a selected set of real places are defined in the file `RayClass.FullModulus`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/RayClass/Basic.lean`: the Lean file is the source byte for byte (SHA-256 `b5348b85fd1bf4a539c3decebab151beda6a75400e9942988846a487446e5a79`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
