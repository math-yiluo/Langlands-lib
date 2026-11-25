# Power indices in the unit groups of a local field

Module `Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.FieldUnitPowerIndexFormulas`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a local field `K` given by a complete discrete valuation `v : K → ℤᵐ⁰` with finite residue field, this file computes the indices `(Kˣ : Kˣⁿ)` and `(O_Kˣ : O_Kˣⁿ)` of `n`-th powers. Writing `p` for the residue characteristic, `μ_n(K)` for the `n`-th roots of unity (the kernel of `x ↦ xⁿ` on `Kˣ`) and `d = [K : ℚ_p]` in characteristic zero, the formulas are `(Kˣ : Kˣⁿ) = n · #μ_n(K) / |n|_p` and `(O_Kˣ : O_Kˣⁿ) = #μ_n(K) / |n|_p`, given both as natural-number identities and as rational ones. Here `|n|_p` is the library's normalized local absolute value (`normalizedLocalNatAbs`), which involves `d`: in the natural-number forms of the mixed case, dividing by it becomes multiplying by `p^(d · v_p(n))`.

## Main results

All results assume `n ≠ 0`.

- `fieldIndex_eq_mul_unitIndex`: in any characteristic, `(Kˣ : Kˣⁿ) = n · (O_Kˣ : O_Kˣⁿ)`; the uniformizer factor contributes exactly `n`.
- Mixed characteristic (`CharZero K`, `v` surjective): `mixed_fieldIndex` gives `(Kˣ : Kˣⁿ) = n · #μ_n(K) · p^(d · v_p(n))` and `mixed_unitIndex` gives `(O_Kˣ : O_Kˣⁿ) = #μ_n(K) · p^(d · v_p(n))`. `mixed_unitIndex_of_coprime`: for `n` prime to `p`, `(O_Kˣ : O_Kˣⁿ) = #μ_n(K)`. `mixed_fieldIndex_rationalFormula` and `mixed_unitIndex_rationalFormula` state the same in `ℚ`, dividing by `normalizedLocalNatAbs p d n`, the library's normalized local absolute value of `n`.
- Equal characteristic (`CharP K p`, `n` prime to `p`): `equal_fieldIndex` gives `(Kˣ : Kˣⁿ) = n · #μ_n(K)` and `equal_unitIndex` gives `(O_Kˣ : O_Kˣⁿ) = #μ_n(K)`, with rational forms using `normalizedLocalNatAbs p 0 n`.

## Proofs

`fieldIndex_eq_mul_unitIndex` only picks a uniformizer and applies a general identity proved elsewhere. The mixed and equal results also use a structure theorem for the first principal units proved elsewhere: `U¹ ≅ ℤ/p^a × ℤ_p^d` in mixed characteristic (`chosenMixed_firstPrincipalUnitStructure_ofWithZeroValuation`) and `U¹ ≅ ∏_ℕ ℤ_p` in equal characteristic (`chosenFirstPrincipalUnitStructure_equalCharacteristic`). They then apply generic index computations for such groups. A private equivalence moves the countable product to the universe of `K`.

## Points to watch

- Finiteness of the quotients involved is assumed as instance arguments: of `Kˣ/Kˣⁿ` in the field-index statements, of `O_Kˣ/O_Kˣⁿ` in `fieldIndex_eq_mul_unitIndex`, and of `U¹/(U¹)ⁿ` in all mixed and equal results except `mixed_unitIndex_of_coprime`, which derives it.
- In equal characteristic only exponents prime to `p` are treated.
- The mixed results require `v` to be surjective. `d` is `Module.finrank ℚ_p K` for the `ℚ_p`-algebra structure supplied by `mixedWithZeroValuationContext v`.
- `#μ_n(K)` is `Nat.card` of the kernel of `powMonoidHom n` on `Kˣ`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/FieldUnitPowerIndexFormulas.lean`: the Lean file is the source byte for byte (SHA-256 `815258677a3c886f1445d79468939aa08ee8a976e7b65457fbe46ff720959191`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
