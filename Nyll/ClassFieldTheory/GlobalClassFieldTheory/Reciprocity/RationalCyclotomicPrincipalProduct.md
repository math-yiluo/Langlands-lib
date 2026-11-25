# Principal ideles have trivial cyclotomic ℤ̂-value

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.RationalCyclotomicPrincipalProduct`, copied from the Lean library NYLL with one local instance replaced (see "Changed declarations"). The origin of the file is given at the end of this page.

This file proves that the global Artin map into the library's rational cyclotomic `ℤ̂`-extension kills every principal idele of `ℚ`, and deduces that the normalised cyclotomic `ℤ̂`-valuation kills principal ideles of any number field. Over the finite places, the local Artin characters of a principal idele multiply to the image of the sign of `x`; the sign is then removed using that `ℤ̂` is torsion-free.

## Main results

- `rationalCyclotomicPrincipalFinitePlaceProduct_eq_sign`: for a prime `p`, `k ≥ 0` and `x : ℚˣ`, the product over all finite places of the cyclotomic characters in `(ZMod (p ^ k))ˣ` of the chosen Artin symbols of the principal idele of `x` is the reduction of the sign unit `rationalSignPadicUnit x p`.
- `rationalCyclotomicGlobalArtin_character_toZModPow_principalFinitePart_eq_sign`: the same holds for the `p`-component of the cyclotomic character (`rationalCyclotomicCharacterPrimeProduct`) of the infinite global Artin symbol in `KummerTheory.rationalCyclotomicField` of the finite part of the principal idele, reduced modulo `p ^ k`. `..._sq`: these reductions have square one.
- `rationalCyclotomicZHatIdeleValue_principalFinitePart_eq_one` and `rationalCyclotomicZHatIdeleValue_principalIdele_eq_one`: `rationalCyclotomicZHatIdeleValue` is trivial on the finite part of a principal idele and on the principal idele itself.
- `normalizedCyclotomicZHatIdeleValue_principalIdele_eq_zero`: for a number field `K` and `x : Kˣ`, `normalizedCyclotomicZHatIdeleValue K` vanishes on the principal idele of `x`.

## Proofs

The product over finite places is the factor at `p`, the reduced `p`-unit part of `x`, times the product of `q ^ (−v_q(x))` over the other primes; by the prime factorisation of `x` this is the reduced sign. The infinite Artin character of the finite part is this finite product (`rationalCyclotomicGlobalArtin_character_toZModPow_finitePart_eq_finprod`). Square one at every `p ^ k` gives triviality in `ℤ̂` (`rationalCyclotomicZHatIdeleValue_eq_one_of_character_reductions`). Over `K`, the criterion `normalizedCyclotomicZHatIdeleValue_principalIdele_eq_zero_iff_finitePart` reduces the claim to the rational principal idele of the norm `Algebra.norm ℚ x`.

## Remarks

- The Artin symbol of the finite part in the full cyclotomic field is not shown trivial: its character reductions equal the sign of `x`. Only the value in the `ℤ̂`-extension is trivial.
- The number field `K` in the last theorem lives in `Type`, universe `0`.

## Changed declarations

The source declares the anonymous local instance `local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩` in namespace `GlobalClassFieldTheory.Reciprocity`. Lean names it from its type, and other modules of the copy declare the same name, so the modules could not be imported together. Here the declaration is replaced by `attribute [local instance] fact_prime_val`, where `GlobalClassFieldTheory.Reciprocity.fact_prime_val : ∀ (p : Nat.Primes), Fact p.1.Prime` (proof `⟨p.2⟩`, module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.PrimesFact`, imported with `public import`) has the same type and proof. The instance stays local to the file; no statement or proof of the file changes otherwise.

## Origin of the file

Copied from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/RationalCyclotomicPrincipalProduct.lean`. The Lean file is the source byte for byte except for the change above (SHA-256 of the source: `d93553ea6db1bc579d71a33de00c706cff7a17d25768bf5af15bdb9bca1db211`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
