# Simple Kummer extensions K(ⁿ√b)

Module `Nyll.GaloisCohomology.Kummer.Concrete.SimpleExtension`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a field `K`, a positive integer `n` nonzero in `K` and a unit `b ∈ Kˣ`, the file chooses an `n`-th root of `b` in Mathlib's `SeparableClosure K` and studies the field it generates. When `K` contains a primitive `n`-th root of unity, this field is a finite cyclic Galois extension whose group has exponent dividing `n`.

## Main definitions

- `chosenSimpleKummerRoot K n hnK b`: a root of `X^n − b` in the separable closure, chosen by `Classical.choose`; `chosenSimpleKummerRoot_pow` says its `n`-th power is `b`.
- `chosenSimpleKummerExtension K n hnK b`: the intermediate field `K(β)` it generates, contained in the maximal Kummer extension (`chosenSimpleKummerExtension_le_maximalKummerExtension`).
- `chosenSimpleKummerRootUnit`: `β` as a unit of `K(β)`.
- `chosenSimpleKummerRootCharacter`: the Kummer character `σ ↦ σ(β)/β`, from `Gal(K(β)/K)` to `μ_n(K(β))`.

## Main results

- `chosenSimpleKummerExtension_adjoin_root_eq_top`: `β`, seen inside `K(β)`, generates it.
- `chosenSimpleKummerExtension_finiteDimensional`: `K(β)/K` is finite, since `β` is integral.
- `chosenSimpleKummerExtension_isAbelianGalois`: with a primitive `n`-th root of unity in `K`, `K(β)/K` is abelian Galois. The proof identifies `K(β)` with the radical extension of a suitable admissible subgroup of finite support and applies the general radical-extension theorem.
- `chosenSimpleKummerRootQuotient_eq_one_iff`, `chosenSimpleKummerRootCharacter_injective`: an automorphism fixing `β` is the identity, so the character is injective.
- `chosenSimpleKummerExtension_isCyclic`: the Galois group is cyclic, because it embeds into the cyclic group `μ_n`.
- `chosenSimpleKummerExtension_galois_pow_eq_one`: every automorphism has `n`-th power `1`.

## Points to watch

- The field depends on a noncomputable choice of root; it is not defined as the splitting field of `X^n − b`.
- The degree of `K(β)/K` is not computed, and nothing says it is cyclic of order exactly `n`.
- `(n : K) ≠ 0` is needed to choose the root; the primitive-root hypothesis is needed for the Galois statements.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/GaloisCohomology/Kummer/Concrete/SimpleExtension.lean`: the Lean file is the source byte for byte (SHA-256 `63625dcc4bb9aaa771909942181998959f79f022edd88d67f6c24568cb2b45ae`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
