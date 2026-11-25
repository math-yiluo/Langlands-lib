# Prime-power detection for the rational cyclotomic ℤ̂-Artin map

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.RationalCyclotomicZHatRigidity`, copied from the Lean library NYLL with one local instance replaced (see "Changed declarations"). The origin of the file is given at the end of this page.

For an idele `a` of `ℚ`, let `σ` be its infinite global Artin symbol in the full rational cyclotomic field `KummerTheory.rationalCyclotomicField`. The file shows that square-one conditions on the prime-power reductions of the cyclotomic character of `σ` pass to the library's rational cyclotomic `ℤ̂`-extension.

- `rationalCyclotomicZHatGlobalArtin_sq_eq_one_of_character_reductions`: if, for every prime `p` and every `k`, the reduction modulo `p ^ k` of the `p`-component `rationalCyclotomicCharacterPrimeProduct σ p` has square one, then `rationalCyclotomicZHatGlobalArtin a` has square one.
- `rationalCyclotomicZHatIdeleValue_eq_one_of_character_reductions`: under the same hypothesis, `rationalCyclotomicZHatIdeleValue a = 1`.

The first result applies `rationalCyclotomicAutomorphism_sq_eq_one_of_character_reductions` to `σ` and restricts to the `ℤ̂`-extension (`rationalCyclotomicFullRestrictionToZHat`). The second uses that squaring is injective on `Multiplicative ZHat`.

The module comment speaks of detecting every finite coordinate; the statements proved are these square-one forms.

## Changed declarations

The source declares the anonymous local instance `local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩` in namespace `GlobalClassFieldTheory.Reciprocity`. Lean names it from its type, and other modules of the copy declare the same name, so the modules could not be imported together. Here the declaration is replaced by `attribute [local instance] fact_prime_val`, where `GlobalClassFieldTheory.Reciprocity.fact_prime_val : ∀ (p : Nat.Primes), Fact p.1.Prime` (proof `⟨p.2⟩`, module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.PrimesFact`, imported with `public import`) has the same type and proof. The instance stays local to the file; no statement or proof of the file changes otherwise.

## Origin of the file

Copied from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/RationalCyclotomicZHatRigidity.lean`. The Lean file is the source byte for byte except for the change above (SHA-256 of the source: `d2b8d8b8587bf94227c330370ee1c98264c36cf23da8dc7c78cbff347c322f95`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
