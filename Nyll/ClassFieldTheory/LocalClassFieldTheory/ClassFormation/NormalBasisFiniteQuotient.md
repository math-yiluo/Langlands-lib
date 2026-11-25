# Deep normal-basis unit subgroups have finite index

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisFiniteQuotient`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `L/K` be a finite Galois extension of nonarchimedean local fields, with `𝒪_L` finite over `𝒪_K`. Write `Vⁿ` for the set `chosenNormalBasisPrincipalUnitSet K L n` of units `u` with `u − 1` in the scaled normal-basis lattice `πⁿM`. The file shows that `Vⁿ` has finite index in `𝒪_Lˣ` for large `n`.

- `exists_principalUnits_le_chosenNormalBasisPrincipalUnitSet`: for `n` large, `Vⁿ` contains a principal-unit group `U_L^(m)`.
- `integerUnitsModPrincipalUnitsToSubgroupQuotient`: the surjection `𝒪_Lˣ/U_L^(m) → 𝒪_Lˣ/V` when `U_L^(m) ≤ V`.
- `finite_chosenNormalBasisIntegerUnitsQuotient_of_principalUnits_le`: such a quotient `𝒪_Lˣ/V` is finite.
- `exists_finite_chosenNormalBasisIntegerUnitsQuotient`: for `n` large, every subgroup `V` with underlying set `Vⁿ` has finite quotient `𝒪_Lˣ/V`.

For large `n` the lattice `πⁿM` is a neighbourhood of `0`, so it contains a power of the maximal ideal of `𝒪_L`; finiteness of `𝒪_Lˣ/U_L^(m)` comes from `integerUnitsModPrincipalUnitsAtLevel_finite_of_isNonarchimedeanLocalField`.

`Vⁿ` is only a set: the statements quantify over subgroups whose carrier equals it. In Lean, `K` and `L` are taken in the same universe, and the valuation of `L` extends that of `K` (`Valuation.HasExtension`).

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/NormalBasisFiniteQuotient.lean`: the Lean file is the source byte for byte (SHA-256 `6b672e611eac45e762a1f9a5748bae8d5342dc3cbb10722ddf5fc3158022c256`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
