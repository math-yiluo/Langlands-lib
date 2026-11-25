# Monic coprime-factor lifting implies Hensel's lemma

Module `Nyll.ValuedFieldTheory.Valuation.Henselian.ValuationExtensionCriterion`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a valuation subring `V` of a field `K`, this file proves that lifting coprime monic factorizations of the reduction of monic polynomials over `V` (Artin's criterion) is equivalent to the library's Hensel factorization property, which lifts coprime factorizations of the reduction of arbitrary polynomials over `V` with nonzero reduction.

## Main results

- `henselianValuationExtension`: `MonicResidualCoprimeFactorLifting V` implies `HenselFactorizationProperty V`.
- `henselianValuationExtension_iff`: the two properties are equivalent. The converse direction is quoted from an earlier file, as the monic special case.
- `primitiveIrreducibleReductionProperty_of_monicResidualCoprimeFactorLifting`: monic lifting implies `PrimitiveIrreducibleReductionProperty V`: for every primitive `Q` over `V` irreducible over `K`, the reduction `Q̄` has degree 0 or degree `deg Q`, and `Q̄` has no factorization into two coprime factors of positive degree.
- `MonicResidualCoprimeFactorLifting.leadingCoeff_unit_branch`: the case where the leading coefficient of `Q` is a unit: then `deg Q̄ = deg Q`, and every factorization of `Q̄` into two coprime factors has a factor of degree 0.

## Proofs

When the leading coefficient of `Q` is a unit, `Q` is rescaled to a monic polynomial, the two residual factors are rescaled to monic ones, and an earlier consequence of monic lifting (a monic irreducible polynomial has no coprime residual splitting into nonconstant factors) applies. Otherwise, `V` is extended to a valuation subring of the splitting field of `Q`; monic lifting forces all roots of `Q` to have the same valuation there, and an earlier result then gives `deg Q̄ = 0`. The Hensel property then follows from an earlier theorem deriving it from `PrimitiveIrreducibleReductionProperty`.

## Points to watch

- All three properties are the library's own definitions, made in earlier files, not Mathlib's `HenselianLocalRing`. `MonicResidualCoprimeFactorLifting V` asks for monic lifts `G, H` of monic coprime `ḡ, h̄` with `f = G · H` for monic `f`. `HenselFactorizationProperty V` asks, for any `f` with nonzero reduction `f̄ = ḡ · h̄`, `ḡ, h̄` coprime, for `G, H` with `f = G · H`, `Ḡ = ḡ`, `H̄ = h̄`, `deg G = deg ḡ` and `deg H ≤ deg f − deg ḡ`.
- The names `henselianValuationExtension` and `henselianValuationExtension_iff` refer to the factor-lifting criterion, not to extensions of valuations.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/Henselian/ValuationExtensionCriterion.lean`: the Lean file is the source byte for byte (SHA-256 `570b758ffe8b70317a0ed143ce35dd6ad69aec8315bc64d019c90a271bf86420`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
