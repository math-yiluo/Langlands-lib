# Cohomology of units in unramified extensions

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.Unramified.Cohomology`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let L/K be a finite unramified Galois extension of nonarchimedean local fields, so that Gal(L/K) is cyclic. The file proves that the degree 0 and degree −1 Tate cohomology groups of 𝒪_L^× and of every higher principal unit group U_L^(n), n ≥ 1, vanish, and that the norm maps 𝒪_L^× → 𝒪_K^× and U_L^(n) → U_K^(n) are surjective.

## Main definitions and results

- `galoisGroupPrincipalUnitsMulDistribMulActionOfIsIntegralClosure K L n`: the action of Gal(L/K) on U_L^(n), for K, L in one universe with valuations, the valuation of L extending that of K, and 𝒪_L the integral closure of 𝒪_K; with a simp lemma for the action.
- `unramified_units_tateCohomology_and_norm_surjective_for_generator`: for K, L : Type nonarchimedean local fields (L with a uniform structure and `IsUniformAddGroup L`), L/K finite Galois, `IsIntegralClosure 𝒪[L] 𝒪[K] L`, `Module.Finite 𝒪[K] 𝒪[L]`, `IsUnramifiedValuedExtension K L`, and g generating Gal(L/K): `HerbrandH0` and `HerbrandHMinusOne` (for g) of 𝒪_L^× and of each U_L^(n), n ≥ 1, are trivial; the norm on 𝒪_L^× and the norms on U_L^(n), n ≥ 1, have full range.
- `unramified_units_tateCohomology_and_norm_surjective`: the same with g the arithmetic Frobenius `arithmeticFrobeniusOfUnramifiedValuation K L`, whose generation property is supplied by `arithmeticFrobeniusOfUnramifiedValuation_generates`.

## Proofs

The Herbrand quotient of 𝒪_L^× is 1, by a normal-basis construction: at a large enough level a principal-unit subgroup with trivial cohomology and finite quotient is chosen. Degree 0 vanishes because a Galois-fixed unit of 𝒪_L comes from 𝒪_K^× (valuation-ring descent) and is a norm by the unramified norm surjectivity; degree −1 then vanishes since the Herbrand quotient is 1. For U_L^(n), the sequence 1 → U_L^(n) → 𝒪_L^× → 𝒪_L^×/U_L^(n) → 1 is shown to be exact and equivariant; the finite quotient has Herbrand quotient 1, so multiplicativity gives Herbrand quotient 1 for U_L^(n), and degree 0 vanishes by surjectivity of the principal-unit norm.

## Caveats

- The cohomology groups are the library's multiplicative `HerbrandH0` and `HerbrandHMinusOne` for a cyclic group with a chosen generator g, not Mathlib's group cohomology; the degree −1 group depends on g.
- The principal-unit statements are for n ≥ 1 only.
- The Galois actions on units are those induced through the integral-closure identification; they are definitions, not global instances, and enter the statements through `letI`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Unramified/Cohomology.lean`: the Lean file is the source byte for byte (SHA-256 `d47c64be132c103becfc296c70ebaeaf9858d0eecdc4b634777c6c43afa7d9bf`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
