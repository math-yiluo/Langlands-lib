# The Galois action on the valuation ring and its filtrations

Module `Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.GaloisIntegerRing`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `L/K` be an extension of fields with valuative relations, the valuation of `L` extending that of `K`, and assume `𝒪[L]` is the integral closure of `𝒪[K]` in `L`. The file restricts `K`-automorphisms of `L` to `𝒪[L]` and carries the resulting action to the ideals of `𝒪[L]`, the principal units `U_Lⁿ`, and the graded pieces `𝓂_Lⁿ/𝓂_L^(n+1)` and `U_Lⁿ/U_L^(n+1)`. It is the equivariance input for cohomological arguments on units.

## Definitions

- `galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ`: the ring automorphism of `𝒪[L]` induced by `σ ∈ Gal(L/K)`. `galoisGroup_mem_integerRing_of_isIntegralClosure` shows `σ` preserves `𝒪[L]`: `σ(x)` is integral over `𝒪[K]`, hence in the integral closure.
- `galoisGroupIntegerRingEquivHomOfIsIntegralClosure` and `galoisGroupIntegerRingMulSemiringActionOfIsIntegralClosure`: the same as a homomorphism `Gal(L/K) →* Aut(𝒪[L])` and as an action.
- The induced actions on ideals (`…IdealDistribMulAction…`), on `U_Lⁿ` (`galoisGroupPrincipalUnitsMapEquivOfIsIntegralClosure`), on `𝓂_Lⁿ/𝓂_L^(n+1)` (additively and multiplicatively written), and on `U_Lⁿ/U_L^(n+1)` (multiplicatively and additively written); all but the ideal action come with a homomorphism into the automorphism group.

## Results

- The action fixes the image of `𝒪[K]`, commutes with `𝒪[K]`-scalars (`SMulCommClass`) and is compatible with the action on `L` (`SMulDistribClass`).
- `galoisGroupIntegerRing_isGaloisGroup_of_isIntegralClosure`: for `L/K` Galois, `Gal(L/K)` acting on `𝒪[L]` is a Galois group of `𝒪[L]` over `𝒪[K]` in Mathlib's sense (`IsGaloisGroup`).
- Every `σ` maps `𝓂[L]` to itself, so `Gal(L/K)` lies in the stabilizer of `𝓂[L]` (`galoisGroupMaximalIdealStabilizerHomOfIsIntegralClosure`).
- For `n ≥ 1`, the comparison `𝓂_Lⁿ/𝓂_L^(n+1) ≃ U_Lⁿ/U_L^(n+1)` (`a ↦ 1 + a`) is Galois-equivariant, additively and multiplicatively.
- `galoisGroup_prod_one_add_sub_one_sub_sum_mem_maximalIdeal_pow_succ_of_isIntegralClosure`: for `L/K` finite, `n ≥ 1` and `a ∈ 𝓂_Lⁿ`, `∏_σ (1 + σa) - 1 - Σ_σ σa ∈ 𝓂_L^(n+1)`.

## Watch for

- No local-field hypothesis is used: apart from the finiteness and Galois assumptions named above, the results need only the valuative relations, the extension property and the integral-closure property, which is an instance hypothesis.
- `Gal(L/K)` is the group of `K`-algebra automorphisms of `L`; only the `IsGaloisGroup` statement assumes `L/K` Galois.
- All actions are definitions supplied with `letI`, not global instances.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/GaloisIntegerRing.lean`: the Lean file is the source byte for byte (SHA-256 `30fd4406c3a9e1467346d096f44da08647101d901579f2ce3e0061cfa1fb1aee`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
