# The finite Kummer character isomorphism

Module `Nyll.GaloisCohomology.Kummer.Concrete.FiniteCharacterEquiv`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite Galois extension `L/K` and `n ≥ 1`, the file builds the group `Δ` of elements of `Kˣ` that are `n`-th powers in `Lˣ`, and proves the Kummer isomorphism `Δ / (Δ ∩ Kˣⁿ) ≅ Hom(Gal(L/K), μ_n(L))`, the class of `a` going to `σ ↦ σ(β)/β` for an `n`-th root `β` of `a`.

## Main definitions and results

- `finiteKummerRadicalSubgroup n`: `Δ = {a ∈ Kˣ | a = βⁿ for some β ∈ Lˣ}`, as a subgroup.
- `chosenFiniteKummerRadicalDatum n`: `Δ` with an arbitrary choice of `n`-th root for each element, made after `Δ` is built; no multiplicativity of the choice is required.
- `NthRootsOfUnityInBase n`: every `n`-th root of unity of `L` comes from `K` (the form of `μ_n ⊆ K` used here). Under it, `nthRootsOfUnity_fixed`: every `σ ∈ Gal(L/K)` fixes these roots.
- `finiteKummerQuotientCharacter_surjective`: for finite Galois `L/K` with `NthRootsOfUnityInBase n`, every homomorphism `Gal(L/K) → μ_n(L)` is the Kummer character of some element of `Δ`.
- `finiteKummerCharacterEquiv`: the isomorphism `Δ / (Δ ∩ Kˣⁿ) ≃* Hom(Gal(L/K), μ_n(L))`.

## Proof

Surjectivity: a character `χ` is a 1-cocycle with values in `Lˣ`, since `σ` fixes `μ_n(L)`; Hilbert's Theorem 90 in Noether's form (Mathlib's `isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units`) gives `β` with `σ(β) = χ(σ) β`; then `βⁿ` is Galois-invariant, so lies in `K`, and its class maps to `χ`. Injectivity and the quotient `RadicalQuotient` come from the library's radical-quotient file.

## Points to watch

- `L/K` need not be abelian here.
- This is only the character-isomorphism half of finite Kummer theory; the correspondence between radical subgroups and abelian extensions is not asserted.
- The roots-of-unity hypothesis is `NthRootsOfUnityInBase`, not a primitive root in `K`; other files derive it from a primitive root.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/GaloisCohomology/Kummer/Concrete/FiniteCharacterEquiv.lean`: the Lean file is the source byte for byte (SHA-256 `06e72019f32bdcde96fe634677057062127ce7370a27977009f3574024b3f69d`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
