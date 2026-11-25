# Primes not dividing the level are unramified in rational cyclotomic fields

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.RationalCyclotomicFinitePlace`, copied from the Lean library NYLL with one local instance replaced (see "Changed declarations"). The origin of the file is given at the end of this page.

The file links Mathlib's ramification-index formula for cyclotomic extensions of `ℚ` to the chosen finite places used by the library's global Artin map.

- `rationalPrime_liesOver_integerSpan`: the height-one prime `RayClass.rationalPrime q` of `𝓞 ℚ` lies over the ideal `(q)` of `ℤ`.
- `rationalCyclotomicLevel_isUnramifiedAt_chosenFinitePlaceCentre`: for `m : ℕ+` and a prime `q ∤ m`, the centre of the chosen extension of the place `q` to the cyclotomic level `rationalCyclotomicLevel m` is unramified over `𝓞 ℚ` (`Algebra.IsUnramifiedAt`).
- `rationalCyclotomicLevel_chosenFinitePlaceIsUnramified`: the same conclusion for the library's predicate `ChosenFinitePlaceIsUnramified`.

Mathlib's `IsCyclotomicExtension.Rat.ramificationIdx_eq_of_not_dvd` gives ramification index `1` over `ℤ`; multiplicativity of ramification indices in the tower `ℤ → 𝓞 ℚ → 𝓞 L` gives index `1` over `𝓞 ℚ`.

`ChosenFinitePlaceIsUnramified` is the library's own predicate, stated at the chosen extension `chosenFinitePlaceExtension` of the place.

## Changed declarations

The source declares the anonymous local instance `local instance (q : Nat.Primes) : Fact q.1.Prime := ⟨q.2⟩` in namespace `GlobalClassFieldTheory.Reciprocity`. Lean names it from its type, and other modules of the copy declare the same name, so the modules could not be imported together. Here the declaration is replaced by `attribute [local instance] fact_prime_val`, where `GlobalClassFieldTheory.Reciprocity.fact_prime_val : ∀ (p : Nat.Primes), Fact p.1.Prime` (proof `⟨p.2⟩`, module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.PrimesFact`, imported with `public import`) has the same type and proof. The instance stays local to the file; no statement or proof of the file changes otherwise.

## Origin of the file

Copied from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/RationalCyclotomicFinitePlace.lean`. The Lean file is the source byte for byte except for the change above (SHA-256 of the source: `d236094352d83310727c52247dc1dc46fa7bb6acc472226c4fe0e66c95e32eb8`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
