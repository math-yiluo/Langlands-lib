# The cyclotomic ZHat-extension of ℚ and its base change to number fields

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.CyclotomicZHatBaseChange`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let ℚ̃ be the cyclotomic ZHat-extension of ℚ, the torsion-fixed subfield of ℚ(μ∞), placed inside the fixed separable closure ℚ̄ = `SeparableClosure ℚ`. This file uses it to define the global degree map of the library's abstract class field theory, Gal(ℚ̄/ℚ) → ZHat. It then studies the composita Kℚ̃ of a number field K with ℚ̃ and the normalizing integer f_K = [K ∩ ℚ̃ : ℚ]. The copy of K, ℚ̃ and the composita are Mathlib intermediate fields of ℚ̄.

## The degree datum over ℚ

- `rationalCyclotomicZHatField`, an abelian Galois intermediate field, with `rationalCyclotomicZHatFieldGalEquivZHat : Gal(ℚ̃/ℚ) ≃ₜ* Multiplicative ZHat`. On restrictions from ℚ(μ∞) this coordinate is the torsion-free component of the cyclotomic character (`..._fullRestriction`). Its Galois group is torsion-free (an instance).
- `rationalCyclotomicDegreeData`: the `DegreeData` whose degree is restriction to ℚ̃ followed by that equivalence; it is surjective.
- Its inertia is the closed subgroup fixing ℚ̃ (`rationalCyclotomicDegreeData_inertia`); the fixed field of the inertia of a closed subgroup H is F ⊔ ℚ̃, with F the fixed field of H.
- The degree image of H is the subgroup of ZHat fixing F ∩ ℚ̃. For H of finite index, the residue degree of H equals [F ∩ ℚ̃ : ℚ] (`rationalCyclotomicDegreeData_residueDegree_eq_intersection_finrank`), and this degree does not depend on the embedding of F into ℚ̄.

## Base change to a number field K

- `cyclotomicZHatIntersectionDegree K` is f_K, computed through the library's chosen embedding `numberFieldSeparableClosureEmbedding`. It is positive and divides [K : ℚ]. Under the ZHat coordinate the subgroup fixing K ∩ ℚ̃ is f_K·ZHat. For an abstract fixed field it equals the residue degree above.
- `numberFieldCyclotomicZHatCompositum K` (Kℚ̃) is abelian Galois over K. `numberFieldCyclotomicZHatCompositumRestriction K : Gal(Kℚ̃/K) →* Gal(ℚ̃/ℚ)` is injective and continuous.
- For a finite Galois layer E of ℚ̃, the compositum KE is abelian Galois over K, and restriction Gal(KE/K) → Gal(E/ℚ) has image the subgroup fixing K ∩ E (`numberFieldCyclotomicZHatFiniteCompositum_restriction_range`).

## Proofs

Independence of the embedding extends it to an automorphism of ℚ̄, which preserves ℚ̃ by normality. Continuity uses `restrictNormalHom_numberFieldCyclotomicZHatCompositumRestriction`: for σ in Gal(Kℚ̃/K), restricting to ℚ̃ then to E agrees with restricting to the copy of KE in Kℚ̃ then to E.

## Points to watch

- The degree datum and its "inertia" are notions of the library's abstract class formation. Here "unramified" means contained in Fℚ̃, not unramified at primes.
- Everything for a bare number field K goes through one chosen embedding of K into ℚ̄; f_K is shown independent of the embedding only for abstract fixed fields.
- The injectivity of restriction to ℚ̃ gives an embedding of Gal(Kℚ̃/K) into Gal(ℚ̃/ℚ), not an isomorphism.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/CyclotomicZHatBaseChange.lean`: the Lean file is the source byte for byte (SHA-256 `6a09f9ebbb021e55536528540136d1f293adc1333f4882b933456ad94a47553d`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
