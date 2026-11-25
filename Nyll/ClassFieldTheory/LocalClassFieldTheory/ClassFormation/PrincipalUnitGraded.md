# Successive quotients of the normal-basis unit filtration

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.PrincipalUnitGraded`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `K` be a nonarchimedean local field with chosen uniformizer `π`, `L/K` a finite Galois extension whose valuation extends that of `K`, `M` the normal-basis lattice and `Vⁿ = 1 + πⁿM` the corresponding set of units of `𝒪_L`. For subgroups `Vn ⊇ Vsucc` of `𝒪_Lˣ` with carriers `Vⁿ` and `Vⁿ⁺¹`, the file compares `Vn/Vsucc` with the lattice quotient `πⁿM / πⁿ⁺¹M` through `u ↦ u − 1`, and shows that the two are isomorphic at deep levels.

## Main results

The comparison homomorphism `chosenNormalBasisPrincipalUnitSuccQuotToLatticeSuccQuotHom`, defined in another file, takes as hypothesis the estimate `hmul_error`: for `u, v ∈ Vⁿ`, `(uv − 1) − ((u − 1) + (v − 1))` lies in `πⁿ⁺¹M`.

- `chosenNormalBasisPrincipalUnitSuccQuotToLatticeSuccQuotHom_injective`: under `hmul_error`, the comparison is injective.
- `chosenNormalBasisPrincipalUnitSuccQuotToLatticeSuccQuotHom_surjective_of_le_maximalIdeal`: if moreover `πⁿM` lies in the maximal ideal of `𝒪_L`, it is surjective.
- `chosenNormalBasisPrincipalUnitSuccQuotMulEquivLatticeSuccQuot`: under both hypotheses, the isomorphism `Vn/Vsucc ≃* Multiplicative (πⁿM / πⁿ⁺¹M)`, sending the class of `u` to the class of `u − 1` (`_mk`).
- `exists_chosenNormalBasisPrincipalUnitSuccQuotMulEquivLatticeSuccQuot`: if `L` is a nonarchimedean local field and `𝒪_L` is finite over `𝒪_K`, there is `c` such that for every `n ≥ c` there are subgroups `Vn ⊇ Vsucc` with carriers `Vⁿ`, `Vⁿ⁺¹`, with `Vn` inside the principal units `U_L^(1)`, and an isomorphism `Φ` as above.

## Proofs

Injectivity amounts to `u − 1 ∈ πⁿ⁺¹M` if and only if `u ∈ Vⁿ⁺¹` (`chosenNormalBasisPrincipalUnitLatticeClass_eq_zero_iff`). For surjectivity, a class represented by `x ∈ πⁿM ⊆ 𝓂_L` is hit by the unit `1 + x`. The existence theorem takes `n` beyond three thresholds established elsewhere: existence of the subgroups (`exists_chosenNormalBasisPrincipalUnitSubgroupSuccPair`), the estimate `hmul_error` (`exists_chosenNormalBasisPrincipalUnitSet_mul_error_mem_succ`), and the bound `πⁿM ⊆ 𝓂_L` (`exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_le_maximalIdeal_and_mul_closed`).

## Points to note

The injectivity carries the multiplicative error estimate, and the surjectivity and the isomorphism also the lattice bound, as explicit hypotheses; only the existence theorem discharges them, for unspecified large `n`. The sets `Vⁿ` are not themselves subgroups; the statements work with subgroups whose carriers equal them. `K` and `L` are taken in the same universe.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/PrincipalUnitGraded.lean`: the Lean file is the source byte for byte (SHA-256 `1672842e2a29739b648c4910932a23b6f8582c9344a49118930a4758442d146e`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
