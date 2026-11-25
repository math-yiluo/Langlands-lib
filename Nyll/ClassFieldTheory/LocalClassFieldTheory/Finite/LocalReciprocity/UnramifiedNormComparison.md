# The norm subgroup of an unramified extension

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UnramifiedNormComparison`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let L/K be a finite unramified Galois extension of nonarchimedean local fields of degree n. The file shows that the norm subgroup N(L^×) consists exactly of the x ∈ K^× whose normalized valuation is divisible by n, so that K^×/N(L^×) ≅ ℤ/nℤ.

## Main definitions and results

Hypotheses: K : Type u and L : Type v nonarchimedean local fields, L/K finite Galois, the valuation of L extending that of K, `IsIntegralClosure 𝒪[L] 𝒪[K] L`, `Module.Finite 𝒪[K] 𝒪[L]`, and `IsUnramifiedValuedExtension K L`.

- `localNormSubgroup_le_unramifiedNormSubgroup`: every norm has valuation divisible by n = `Module.finrank K L`, i.e. lies in `unramifiedNormSubgroup K n`.
- `normQuotientToUnramifiedNormQuotient`: the induced map K^×/N(L^×) → K^×/`unramifiedNormSubgroup K n`, with `_mk` and `_surjective`; `normQuotientToUnramifiedNormQuotient_injective`.
- `galoisGroupEquivAbelianizationOfUnramifiedValuation`: Gal(L/K) is cyclic, hence isomorphic to its abelianization by the canonical map.
- `normSubgroup_eq_unramifiedNormSubgroup_of_isIntegralClosure`: N(L^×) = `unramifiedNormSubgroup K n`.
- `normQuotientUnramifiedValuationEquivZModOfIsIntegralClosure`: K^×/N(L^×) ≃* `Multiplicative (ZMod n)`, sending the class of x to its valuation reduced mod n (`valuationModDegreeMulHom`).

## Proof

The inclusion comes from v_K(N y) = f · v_L(y) with residue degree f = n. For the reverse, the norm quotient has n elements: finite local reciprocity, applied to `Shrink.{0}` copies of K and L, identifies it with the abelianization of the Galois group, which is cyclic of order n. The valuation quotient also has n elements, so the surjective comparison map is bijective.

## Caveats

The reverse inclusion (an element whose valuation is divisible by n is a norm) is obtained from finite local reciprocity by counting, not by constructing norms.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/UnramifiedNormComparison.lean`: the Lean file is the source byte for byte (SHA-256 `1a059c03c3034773d507dff90023dc30dc1c324c7512301347730ab525e33337`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
