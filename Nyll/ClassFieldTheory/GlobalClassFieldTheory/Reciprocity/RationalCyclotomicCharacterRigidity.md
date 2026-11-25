# A square-one test for automorphisms of the rational cyclotomic field

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.RationalCyclotomicCharacterRigidity`, copied from the Lean library NYLL with one local instance replaced (see "Changed declarations"). The origin of the file is given at the end of this page.

The file gives one consequence of the injectivity of the cyclotomic character of the full rational cyclotomic field `KummerTheory.rationalCyclotomicField`.

- `rationalCyclotomicAutomorphism_sq_eq_one_of_character_reductions`: let `σ` be a `ℚ`-automorphism of this field. If, for every prime `p` and every `k`, the reduction modulo `p ^ k` of the `p`-component `rationalCyclotomicCharacterPrimeProduct σ p ∈ ℤ_[p]ˣ` has square one, then `σ ^ 2 = 1`.

The proof applies the injectivity of `rationalCyclotomicCharacterPrimeProduct` (the character into the product of the `ℤ_[p]ˣ`) and the fact that an element of `ℤ_[p]` is determined by its reductions modulo all `p ^ k`.

The module comment says the character is detected by its prime-power reductions; the only statement proved here is this square-one case.

## Changed declarations

The source declares the anonymous local instance `local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩` in namespace `GlobalClassFieldTheory.Reciprocity`. Lean names it from its type, and other modules of the copy declare the same name, so the modules could not be imported together. Here the declaration is replaced by `attribute [local instance] fact_prime_val`, where `GlobalClassFieldTheory.Reciprocity.fact_prime_val : ∀ (p : Nat.Primes), Fact p.1.Prime` (proof `⟨p.2⟩`, module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.PrimesFact`, imported with `public import`) has the same type and proof. The instance stays local to the file; no statement or proof of the file changes otherwise.

## Origin of the file

Copied from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/RationalCyclotomicCharacterRigidity.lean`. The Lean file is the source byte for byte except for the change above (SHA-256 of the source: `589fb13f727cde20fa241c9bbb54ae3f567a728450030cb6e3fe2491b5b75e26`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
