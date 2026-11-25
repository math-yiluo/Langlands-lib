# Primitive roots of unity from finite p-adic Lubin–Tate levels

Module `Nyll.ClassFieldTheory.LubinTate.Padic.MultiplicativeEvaluation.FiniteLevelPrimitiveRoot`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a prime `p` and a level `n`, the finite standard Lubin–Tate level over ℚ_p for the uniformizer `p` contains a primitive point λ. Applying the comparison series H from the standard to the multiplicative formal group gives ζ = 1 + H(λ). This file proves that ζ is a primitive p^(n+1)-th root of unity and that the Lubin–Tate Galois automorphism attached to a unit `u` of ℤ_p acts on ζ by raising it to the power `u` modulo p^(n+1).

## Main definitions and results

- `padicMultiplicativePrimitiveRoot p n`: the element ζ = 1 + `padicMultiplicativePrimitivePoint p n` of the level field `standardLubinTateLevelField`.
- `padicMultiplicativePrimitiveRoot_isPrimitiveRoot`: ζ is a primitive root of unity of order p^(n+1), in Mathlib's sense `IsPrimitiveRoot`.
- `padicMultiplicativePrimitiveRoot_unitParameterGaloisAction`: the Galois automorphism `standardLubinTateUnitParameterEquivGal` of the unit-parameter class of `u` sends ζ to ζ^m, where m is the natural-number representative (`ZMod.val`) of the reduction of `u` modulo p^(n+1) (`PadicInt.toZModPow`).
- `padicMultiplicativePrimitiveRoot_galoisAction`: equivalently, the inverse of that automorphism sends ζ to the power given by `u⁻¹` modulo p^(n+1). The file calls this the explicit cyclotomic norm-residue formula.

## Proofs

Several private lemmas carry the argument. The multiplicative endomorphism with linear coefficient a natural number m is (1 + X)^m − 1, by uniqueness of the endomorphism with a given linear term. The action of `u` on λ equals that of m, because the endomorphism of anything in 𝔪^(n+1) kills λ. Using the functional equation of H, (1 + H(λ))^(pⁱ) = 1 + H(λᵢ), with λᵢ the i-th iterate of λ under the standard series. Since λ_(n+1) = 0 and H(0) = 0, ζ^(p^(n+1)) = 1. If ζ^(pⁿ) were 1, then H(λₙ) = 0, so λₙ = 0 by injectivity of H, contradicting the finiteness of its valuation. For the Galois action, an automorphism over ℚ_p preserves the valuation ring (an integral closure), is continuous and fixes coefficients, so it commutes with evaluation of H; the inverse of the automorphism of the class of `u` sends λ to the action of `u⁻¹` on λ.

## Points to watch

- Level `n` corresponds to roots of unity of exact order p^(n+1), not pⁿ.
- Orientation: the automorphism of the class of `u` raises ζ to the power `u`; its inverse to the power `u⁻¹`. The statements concern the library's Lubin–Tate unit-parameter automorphism; no reciprocity map appears in this file.
- Everything is for the uniformizer `p` of ℚ_p only.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LubinTate/Padic/MultiplicativeEvaluation/FiniteLevelPrimitiveRoot.lean`: the Lean file is the source byte for byte (SHA-256 `7999c8cd2b900d56fd59731e8d372a3e3ed1b0e2ea4abcf06b37289d0a6ed06d`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
