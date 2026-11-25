# The local Artin map on p-adic cyclotomic Lubin–Tate levels

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.LubinTateApplication.PadicMultiplicativeArtinComparison`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For K = ℚ_p with uniformizer p and the multiplicative Lubin–Tate series, the standard level field T_n = `standardLubinTateLevelField hπ n` contains a chosen primitive p^(n+1)-th root of unity ζ = `padicMultiplicativePrimitiveRoot p n`. The file computes the library's abelian local Artin map of T_n/ℚ_p: p maps to 1, a unit u ∈ ℤ_p^× maps to the explicit Lubin–Tate automorphism attached to u, so that ζ ↦ ζ^(u mod p^(n+1)), and the norm group of T_n is ⟨p⟩ · U^(n+1).

## Main definitions and results

- `padicCompletedChangedUniformizerNegativePrimeUnit p n u`: the unit −θ of the auxiliary field D attached to the changed uniformizer u·p; its norm to ℚ_p is u·p (`_norm`) and its `valuationMap` is −1 (`_valuationMap`).
- `padicCompletedChangedUniformizerRelativeArtin_negativePrime`: for the unramified extension M/D (M a compositum with T_n), the Artin image of −θ is the inverse arithmetic Frobenius, packaged as `padicCompletedChangedUniformizerRelativeArtinCandidate`; `..._restrict_standardLevel`: restricted to T_n it is the unit-parameter automorphism of u.
- `padicMultiplicativeAbelianLocalArtin_baseUniformizer` (Art(p) = 1, p being a norm), `..._eq_uniformizerUnitPart` (Art(x) depends only on the unit part of x) and `..._changedUniformizer` (Art(u·p) = Art(u)).
- `padicMultiplicativeAbelianLocalArtin_eq_unitParameter`: Art(u) = `standardLubinTateUnitParameterEquivGal` of the class of u; `padicMultiplicativeAbelianLocalArtin_primitiveRoot`: Art(u)(ζ) = ζ^(u mod p^(n+1)).
- `..._eq_one_of_mem_higherPrincipalUnitGroup`: Art(u) = 1 for u ∈ U^(n+1), because such u is a norm.
- `padicMultiplicativeArtinUnitParameterHom` and `padicMultiplicativeArtinUnitParameterEquiv`: the Artin map induces ℤ_p^×/U^(n+1) ≅ Gal(T_n/ℚ_p) (surjective, then bijective by counting).
- `padicMultiplicativeUniformizerHigherPrincipalUnitSubgroup p n` = ⟨p⟩ · U^(n+1); `padicMultiplicativeAbelianLocalArtin_ker` and `padicMultiplicativeLocalNormSubgroup_eq_uniformizerHigherPrincipalUnitSubgroup`: it is the kernel of the Artin map and the norm subgroup of T_n.
- `..._eq_unitParameter_of_mem_higherPrincipalUnitGroup`, `..._primitiveRoot_of_mem_higherPrincipalUnitGroup`: for u ∈ U^(n+1), Art(u) is the inverse of the unit-parameter automorphism, and ζ ↦ ζ^(u⁻¹ mod p^(n+1)).

## Proof

Norm–restriction applied to −θ ∈ D^× (norm u·p, valuation −1) and the unramified extension M/D: the image is Frob⁻¹ on M, which restricts to the explicit u-action on T_n, while Art(u·p) = Art(u) since p is a norm.

## Caveats

- Convention: an element with `valuationMap` −1 (such as −θ) goes to the inverse arithmetic Frobenius; correspondingly u acts on ζ by ζ ↦ ζ^u, not ζ^(u⁻¹).
- The two statements with an inverse concern u ∈ U^(n+1), where u ≡ 1 mod p^(n+1) and both sides are trivial; they say nothing about orientation. The general comparison is `padicMultiplicativeAbelianLocalArtin_eq_unitParameter`.
- The docstring of `padicMultiplicativeArtinUnitParameterEquiv` stresses that it is built from the Artin map alone, without reference to the explicit Lubin–Tate equivalence.
- Only ℚ_p, the uniformizer p and the multiplicative series are treated.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/LubinTateApplication/PadicMultiplicativeArtinComparison.lean`: the Lean file is the source byte for byte (SHA-256 `002bf925545b1fa2062d19f7dfa15fdfce4cbf7629ad15ac7325f9cc1b7a69da`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
