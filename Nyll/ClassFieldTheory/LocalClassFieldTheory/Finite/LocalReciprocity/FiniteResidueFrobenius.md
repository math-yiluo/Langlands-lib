# Frobenius coordinates on Galois groups of finite fields

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteResidueFrobenius`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite extension `L / k` of finite fields, the arithmetic Frobenius `x ↦ x ^ #k` generates `Gal(L / k)`. This file turns that into canonical coordinates: an isomorphism `ℤ/[L : k]ℤ ≃ Gal(L / k)` sending `1` to Frobenius, and a continuous surjection `ℤ̂ → Gal(L / k)` through reduction modulo `[L : k]`, both compatible with restriction in towers. The header describes this as the finite-level source of the degree map used in local reciprocity.

## Main definitions and results

Here `Frob` is Mathlib's `FiniteField.frobeniusAlgEquivOfAlgebraic k L`.

- `finiteResidueFrobeniusIntegerPowers k L`: the map `m ↦ Frob ^ m` from `ℤ`, written additively; it vanishes at `[L : k]` (`finiteResidueFrobeniusIntegerPowers_degree_eq_zero`).
- `finiteResidueFrobeniusExponentHom k L`: the induced homomorphism `ZMod [L : k] → Gal(L / k)`, with `m ↦ Frob ^ m` (`finiteResidueFrobeniusExponentHom_intCast`) and `1 ↦ Frob`. It is surjective because every automorphism is a power of Frobenius, and injective by counting, since `#Gal(L / k) = [L : k]`.
- `finiteResidueFrobeniusExponentEquiv`: the resulting isomorphism.
- `finiteResidueFrobeniusFromZHat k L`: the continuous homomorphism from `ℤ̂` (in its multiplicative form `ZHatMul`) obtained by composing reduction `zHatReduction` modulo `[L : k]` with the above. It sends `1` to `Frob`, is surjective, and `z` acts trivially exactly when `z ≡ 0` modulo `[L : k]`.

For a tower `k ⊆ E ⊆ F` of finite fields with `[Normal k E]`:

- `restrictNormalHom_finiteResidueFrobenius`: the Frobenius of `F` restricts to the Frobenius of `E`.
- `restrictNormalHom_finiteResidueFrobeniusExponentHom`: restriction corresponds to reduction `ZMod [F : k] → ZMod [E : k]`.
- `restrictNormalHom_finiteResidueFrobeniusFromZHat`: the `ℤ̂`-actions commute with restriction (via `zHatReduction_transition`).

## Points to watch

- No generator is chosen: the generator is always the arithmetic Frobenius `x ↦ x ^ #k`.
- In the tower results normality of `E` over `k` is an instance argument.
- The fields may lie in different universes.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteResidueFrobenius.lean`: the Lean file is the source byte for byte (SHA-256 `280e4bcadc912462c347b144fb05c920d1b423012e94fad00584176c6b3432f6`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
