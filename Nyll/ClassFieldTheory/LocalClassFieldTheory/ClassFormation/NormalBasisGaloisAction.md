# Galois action on the normal-basis unit subgroups

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisGaloisAction`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file sets up the Galois actions in the exact sequence `1 → V → 𝒪_Lˣ → 𝒪_Lˣ/V → 1`, where `V` is a subgroup of units with underlying set `Vⁿ = 1 + πⁿM`, `M` the normal-basis lattice and `π` the chosen uniformizer of `K`.

## General constructions

For a group `G` acting by automorphisms on a commutative group `A` and a subgroup `V` stable under `G`:

- `subgroupMulDistribMulActionOfStable`: the restricted action on `V`.
- `quotientActionOfSubgroupStable`, `quotientMulDistribMulActionOfSubgroupStable`: the induced action on `A/V`.

## The normal-basis subgroups

Here `K` is a nonarchimedean local field, `L/K` is finite Galois, the valuation of `L` extends that of `K`, and `𝒪_L` is the integral closure of `𝒪_K`. The Galois action on `𝒪_Lˣ` is `galoisGroupIntegerUnitsMulDistribMulActionOfIsIntegralClosure`.

- `galoisGroup_apply_mem_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice`: every `πⁿM` is stable under `Gal(L/K)`.
- `galoisGroup_smul_mem_chosenNormalBasisPrincipalUnitSet`: the set `Vⁿ` is stable under the Galois action on `𝒪_Lˣ`.
- `chosenNormalBasisPrincipalUnitSubgroupMulDistribMulAction`, `chosenNormalBasisIntegerUnitsQuotMulDistribMulAction`: the actions on `V` and on `𝒪_Lˣ/V`, for any subgroup `V` with carrier `Vⁿ`.
- `chosenNormalBasisPrincipalUnitSubgroup_tateNorm_coe`, `chosenNormalBasisPrincipalUnitSubgroup_sigmaMinusOne_coe`: the norm and the operator `σ − 1` on `V` are computed in `𝒪_Lˣ`.
- `chosenNormalBasisPrincipalUnitSubgroupInclusion`, `chosenNormalBasisIntegerUnitsQuotientMap`: the inclusion and the quotient map; both are equivariant, the first is injective, the second surjective, and `chosenNormalBasisPrincipalUnitSubgroupInclusion_range_eq_ker_quotient` gives exactness in the middle.

## Points to note

- The actions are definitions marked `@[implicit_reducible]`, not instances, and those on `V` and `𝒪_Lˣ/V` depend on the proof that the carrier of `V` equals `Vⁿ`.
- The stability of `Vⁿ` comes from the stability of `M` under `Gal(L/K)`, proved elsewhere (`galoisGroup_apply_mem_chosenNormalBasisIntegerLattice`).
- No local-field hypothesis on `L` is made in this file.
- `K` and `L` are taken in the same universe (`K L : Type u`).

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/NormalBasisGaloisAction.lean`: the Lean file is the source byte for byte (SHA-256 `f18de556a13f467390183fab9b45726f6182103e02d0347ad32ac3aaaf95a6aa`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
