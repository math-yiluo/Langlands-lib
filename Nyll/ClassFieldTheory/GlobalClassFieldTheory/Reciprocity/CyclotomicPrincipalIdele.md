# Principal ideles and the rational cyclotomic value: the archimedean part

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.CyclotomicPrincipalIdele`, copied from the Lean library NYLL with one local instance replaced (see "Changed declarations"). The origin of the file is given at the end of this page.

The file reduces the vanishing of the cyclotomic value on principal ideles to a statement about finite places. A rational idele splits into an archimedean part and a finite part. The Artin image of the archimedean part in the cyclotomic ℤ̂-extension T of ℚ is trivial, so only the finite part matters, and at each finite cyclotomic layer its image is the finite product of the chosen local Artin symbols.

## Main definitions and results

- `finiteSubfieldOfRationalCyclotomicField_le_level`: every finite subextension of the library's ℚ(μ∞) (`KummerTheory.rationalCyclotomicField`) lies in some level ℚ(μ_n). `finiteSubfieldOfRationalCyclotomicZHatField_mapsIntoLevel` gives the same for the finite Galois layers of T, up to isomorphism.
- `rationalCyclotomicZHatGlobalArtin_eq_fullRestriction`: the Artin map to T is the restriction of the infinite Artin map to ℚ(μ∞); here T is the lift of the torsion-fixed subfield. `rationalCyclotomicZHatIdeleValue_eq_fullCharacterFreePart`: v_ℚ(a) is the torsion-free component, under `zHatUnitsDecomposition`, of the cyclotomic character of that Artin automorphism.
- `rationalIdeleArchimedeanPart` and `rationalIdeleFinitePart`, with product equal to the idele (`rationalIdeleArchimedeanPart_mul_finitePart`).
- `globalArtinMonoidHom_rationalIdeleArchimedeanPart_sq`: for a finite abelian L/ℚ, the Artin image of the archimedean part has square 1.
- `rationalCyclotomicZHatGlobalArtin_rationalIdeleArchimedeanPart` (simp): the Artin map to T kills the archimedean part. Hence `rationalCyclotomicZHatIdeleValue_eq_finitePart`: v_ℚ depends only on the finite part.
- `rationalCyclotomicGlobalArtin_character_toZModPow` and its `_finitePart`, `_finitePart_eq_finprod` forms: the reduction mod p^k of the p-component of the cyclotomic character of the Artin symbol is the finite Artin symbol at level p^k, read in (ℤ/p^k)ˣ. For the finite part this is the product over finite places of the chosen local Artin characters.
- `restrictNormalHom_rationalCyclotomicZHatGlobalArtin_finitePart`: on a finite layer of T, the image of the finite part is the product of the chosen local Artin symbols.
- `normalizedCyclotomicZHatIdeleValue_principalIdele_eq_zero_iff_finitePart`: for a number field K and x ∈ Kˣ, v_K vanishes on the principal idele of x iff v_ℚ is 1 on the finite part of the principal idele of the field norm of x.

## Proofs

At a finite layer, the Artin image of the archimedean part squared is the infinite Artin factor of a positive real number, hence 1. Finite layers detect Gal(T/ℚ), so the square of the image in T is 1. That group is torsion-free, so the image itself is 1.

## Watch for

- The file does not prove that principal ideles have trivial value. The last result only reduces that to the triviality of the finite product. By its header, proving that product trivial needs a compatibility between the chosen finite-place Artin maps and the explicit cyclotomic action, and this file neither proves nor assumes it.
- The Artin maps are the library's own, built from chosen local factors.
- The number fields `K` and `L` are taken in `Type` (universe 0).

## Changed declarations

The source declares the anonymous local instance `local instance (p : Nat.Primes) : Fact p.1.Prime := ⟨p.2⟩` in namespace `GlobalClassFieldTheory.Reciprocity`. Lean names it from its type, and other modules of the copy declare the same name, so the modules could not be imported together. Here the declaration is replaced by `attribute [local instance] fact_prime_val`, where `GlobalClassFieldTheory.Reciprocity.fact_prime_val : ∀ (p : Nat.Primes), Fact p.1.Prime` (proof `⟨p.2⟩`, module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.PrimesFact`, imported with `public import`) has the same type and proof. The instance stays local to the file; no statement or proof of the file changes otherwise.

## Origin of the file

Copied from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/CyclotomicPrincipalIdele.lean`. The Lean file is the source byte for byte except for the change above (SHA-256 of the source: `f4a2d93ae7cb248e9afda1d8dd6b50b0b4c9ddf0ae09d1c8f69347c2ee82f8ef`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
