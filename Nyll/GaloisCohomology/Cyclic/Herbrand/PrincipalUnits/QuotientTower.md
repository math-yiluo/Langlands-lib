# The tower of unit quotients 𝒪ˣ/Uⁿ and their Herbrand quotients

Module `Nyll.GaloisCohomology.Cyclic.Herbrand.PrincipalUnits.QuotientTower`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a field with a valuative relation, the file studies the quotients `𝒪_Kˣ/U_K^n` of the integral units by the principal units of level n: the maps between levels, the exact sequence `U^n/U^(n+1) → 𝒪ˣ/U^(n+1) → 𝒪ˣ/U^n`, the Galois action when L/K is an extension whose valuation ring of L is the integral closure of that of K, finiteness over a nonarchimedean local field, and the behaviour of the Herbrand quotient along the tower.

## Main definitions and results

- `integerUnitsModPrincipalUnitsMapOfLe` (for n ≤ m) and `integerUnitsModPrincipalUnitsSuccMap` are the projections between levels; the latter is surjective.
- `integerUnitsModPrincipalUnitsMapEquivOfIntegerRingEquiv`: a ring automorphism of `𝒪[K]` induces an automorphism of `𝒪_Kˣ/U_K^n`.
- `principalUnitsSuccQuotToIntegerUnitsModPrincipalUnitsSucc` maps `U^n/U^(n+1)` (the library's `PrincipalUnitsSuccQuot`) into `𝒪ˣ/U^(n+1)`; it is injective and its range is the kernel of the projection to level n.
- `galoisGroupIntegerUnitsModPrincipalUnitsMulDistribMulActionOfIsIntegralClosure` is the action of `Gal(L/K)` on `𝒪_Lˣ/U_L^n`, assuming the valuation of L extends that of K and `𝒪[L]` is the integral closure of `𝒪[K]` in L. Both maps of the exact sequence are equivariant.
- Finiteness: level 0 is trivial; level 1 is the residue units; `integerUnitsModPrincipalUnitsAtLevel_finite_of_isNonarchimedeanLocalField` gives finiteness at every level for a nonarchimedean local field, by induction through the graded pieces.
- For L a nonarchimedean local field, finite `Gal(L/K)` and a generator σ, the degree 0 and −1 Tate groups of `𝒪_Lˣ/U_L^n` are finite and its Herbrand quotient is 1.
- `integerUnitsModPrincipalUnitsSucc_herbrandQuotient_exact_multiplicative_of_isIntegralClosure`: the Herbrand quotient at level n+1 is the product of those of `U^n/U^(n+1)` and of level n. `integerUnitsModPrincipalUnitsSucc_herbrandQuotient_eq_one_of_isIntegralClosure`: if the outer two are 1, so is the middle.

## Proof

Everything is reduced to representatives with the quotient interface of the previous file. The Herbrand statements apply the library's multiplicativity of Herbrand quotients in short exact sequences and its result that a finite module has Herbrand quotient 1.

## Watch for

- The two tower theorems carry the finiteness of all six Tate groups (`hA0`, `hAm`, `hB0`, `hBm`, `hC0`, `hCm`) as hypotheses, and the last one also takes as hypotheses that the Herbrand quotients of `U^n/U^(n+1)` and of level n are 1 (`hA`, `hC`). They assume no local-field structure on L.
- Cyclicity of `Gal(L/K)` is the explicit hypothesis `hgen` with a chosen generator σ.
- Herbrand quotients are the library's own, for multiplicatively written modules.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/GaloisCohomology/Cyclic/Herbrand/PrincipalUnits/QuotientTower.lean`: the Lean file is the source byte for byte (SHA-256 `409df4f3f8c44974bcd26d7631ff390d15663f97e710b9ed2e3f5ee9388571f1`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
