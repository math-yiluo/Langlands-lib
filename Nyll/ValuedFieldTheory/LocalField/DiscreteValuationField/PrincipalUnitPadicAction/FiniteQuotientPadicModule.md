# ℤ_p-module structure on the finite principal-unit quotients

Module `Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnitPadicAction.FiniteQuotientPadicModule`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `F` be a local field with residue field of cardinality q = p^f. The quotients U¹/U^(n+1) of the first principal units are finite groups of order p^(f·n). The file proves this count, deduces that p^(f·n) kills each quotient, and makes each quotient a module over the p-adic integers ℤ_p through reduction ℤ_p → ℤ/p^(f·n), with continuous scalar action and ℤ_p-linear transition maps.

## Main definitions and results

- `principalUnitResidueDegree F`: a positive integer f, chosen so that the residue field has p^f elements, p the residue characteristic. `residueCharacteristic_prime_and_card_eq_pow_residueDegree` states that p is prime and the residue field has p^f elements; `principalUnitResidueDegree_unique` states that any d with the same property equals f.
- `card_discretePrincipalUnitQuotient_eq_residueCharacteristic_pow` (and its `Internal` version on the multiplicative carrier): the n-th quotient has p^(f·n) elements. Finiteness instances are given for both forms.
- `discretePrincipalUnitQuotient_nsmul_residueCharacteristic_pow_eq_zero`: p^(f·n) • x = 0 in the n-th quotient (Lagrange's theorem).
- `Internal.principalUnitQuotientCarrierZModModule`: the resulting ℤ/p^(f·n)-module structure, a definition rather than an instance.
- `discretePrincipalUnitQuotientPadicModule`: the ℤ_p-module instance on the wrapper `DiscretePrincipalUnitQuotient`, obtained by restriction of scalars along `PadicInt.toZModPow (f·n)` and transport through the additive equivalence with the carrier.
- `continuous_discretePrincipalUnitQuotientPadic_smul`: the action ℤ_p × (n-th quotient) → (n-th quotient) is jointly continuous, the quotient carrying the discrete topology.
- `DiscretePrincipalUnitQuotient.transitionLinear`: for m ≤ n, the reduction from level n to level m as a ℤ_p-linear map.

## Proofs

The count rests on the library's computation #(U¹/U^(n+1)) = q^n with a chosen uniformizer. Continuity combines continuity of ℤ_p → ℤ/p^k with discreteness. Linearity of the transitions is the compatibility of `toZModPow` with the cast ℤ/p^(f·n) → ℤ/p^(f·m) (`PadicInt.cast_toZModPow`).

## Points to note

- The index is shifted: the n-th quotient is U¹/U^(n+1), so level 0 is trivial and the order is q^n.
- f is selected by choice from Mathlib's `FiniteField.card`; it is the degree of the residue field over 𝔽_p, and `principalUnitResidueDegree_unique` is what ties it to any other description of that degree.
- `LocalField` is the library's structure, not a Mathlib class: a field with a chosen complete discrete valuation (`CompleteDVF`) and finite residue field.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/PrincipalUnitPadicAction/FiniteQuotientPadicModule.lean`: the Lean file is the source byte for byte (SHA-256 `43f431baad4a18607bd2fea1269dbb26ae40b9c3c3e349fc81f31e8ab7dc0714`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
