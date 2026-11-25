# Ring automorphisms acting on the filtrations of 𝒪[K] and of the principal units

Module `Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.PrincipalUnitActions`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `K` be a field with a valuative relation, `𝒪[K]` its valuation ring and `𝓂[K]` the maximal ideal. A ring automorphism `e` of `𝒪[K]` (for instance one coming from a Galois automorphism) preserves the powers `𝓂^n`, the principal unit groups `U^n`, and so induces automorphisms of the successive quotients `𝓂^n/𝓂^(n+1)` and `U^n/U^(n+1)`. This file constructs these induced maps and shows that the comparison `𝓂^n/𝓂^(n+1) ≃ U^n/U^(n+1)`, induced by `a ↦ 1 + a`, commutes with them.

## Main definitions and results

- `integerRingEquiv_mem_maximalIdeal`, `integerRingEquiv_map_maximalIdeal_pow`, `integerRingEquiv_mem_maximalIdeal_pow`: `e` maps `𝓂` and every `𝓂^n` onto itself.
- `maximalIdealPowMapEquivOfIntegerRingEquiv`: the induced additive automorphism of `𝓂^n`.
- `maximalIdealPowSuccQuotMapEquivOfIntegerRingEquiv` (with its homomorphism form `maximalIdealPowSuccQuotMapOfIntegerRingEquiv` and a multiplicative-notation copy): the induced automorphism of `𝓂^n/𝓂^(n+1)`, with inverse induced by `e⁻¹`.
- `principalUnitsMapEquivOfIntegerRingEquiv`: the induced automorphism of `U^n`; `principalUnitsMapEquivOfIntegerRingEquiv_oneAdd` says it sends `1 + a` to `1 + e(a)`.
- `principalUnitsSuccQuotMapEquivOfIntegerRingEquiv` and its additive form `principalUnitsSuccQuotAddEquivOfIntegerRingEquiv`: the induced automorphism of `U^n/U^(n+1)`.
- `principalUnitsSuccQuotOfMaximalIdealPowSuccQuot_integerRingEquiv`, `maximalIdealPowSuccQuotAddEquivPrincipalUnitsSuccQuot_integerRingEquiv`, `maximalIdealPowSuccQuotMulEquivPrincipalUnitsSuccQuot_integerRingEquiv`: for `n ≥ 1`, the comparison map `𝓂^n/𝓂^(n+1) → U^n/U^(n+1)` and its additive and multiplicative isomorphism forms are equivariant for `e`.

Each induced map is computed on representatives by a `rfl` or `simp` lemma.

## Proofs

A ring automorphism maps nonunits to nonunits, hence fixes `𝓂` and its powers. The maps on quotients come from the lifting principles for `MaximalIdealPowSuccQuot` and `PrincipalUnitsSuccQuot` in the imported file on principal-unit quotients, and equivariance is checked on representatives `1 + a`.

## Points to watch

- Only `[Field K] [ValuativeRel K]` is assumed; nothing here needs a local field.
- Despite the title "actions", no group action is defined: each automorphism `e` gives its own equivalence, and compatibility with composition of automorphisms is not stated.
- The comparison statements require `1 ≤ n`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/PrincipalUnitActions.lean`: the Lean file is the source byte for byte (SHA-256 `80975f170dc8e29609bcfeb74a809331b634ca26ed056a8bca7fbd10029facba`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
