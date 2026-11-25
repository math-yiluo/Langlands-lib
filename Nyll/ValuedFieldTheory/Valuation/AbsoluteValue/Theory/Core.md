# Higher unit groups and graded pieces of a discrete valuation ring

Module `Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.Theory.Core`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a ring `O` with a distinguished element `π` (in the applications a discrete valuation ring with a uniformizer, or the ring of a normalized exponential valuation `v` with a prime element), the file sets up the filtration `π^n O`, its graded pieces, the higher unit groups `U⁽ⁿ⁾` (the units of `O` congruent to `1` modulo `π^n O`), and the standard isomorphisms `Oˣ/U⁽ⁿ⁾ ≅ (O/π^n O)ˣ` and `U⁽ⁿ⁾/U⁽ⁿ⁺¹⁾ ≅ O/(π)`.

## Main definitions and results

- `uniformizerPowerIdeal_primeElement_eq_maximalIdeal_pow_of_normalized`: for a normalized exponential valuation and a prime element `π`, `π^n O = 𝔪^n`.
- `residue_addEquiv_maximalIdeal_pow_quotient` and `residue_addEquiv_uniformizerPowerIdeal_quotient`: additive equivalences `O/𝔪 ≃+ 𝔪^n/𝔪^(n+1)`.
- `uniformizerGradedPiece π n`: the `O`-module `π^n O / π^(n+1) O`, with its quotient map, lifting of linear maps, induction principle and kernel criterion.
- `HigherUnit π n u` and `higherUnitSubgroup π n`: units `u = 1 + π^n a`, a subgroup of `Oˣ`, decreasing in `n`, equal to `Oˣ` for `n = 0`.
- `unitReduction I : Oˣ →* (O/I)ˣ`; `unitReduction_ker_powerIdeal`: its kernel for `I = π^n O` is `U⁽ⁿ⁾`.
- `units_quotient_equiv`: in a DVR with `π` irreducible and `n ≥ 1`, `Oˣ/U⁽ⁿ⁾ ≃* (O/π^n O)ˣ`, induced by reduction (`units_quotient_equiv_mk`). `unitsModMaximalIdealPowEquivOfNormalized` is the version for a normalized exponential valuation and `𝔪^n`.
- `higherUnitCoeffModHom`: for a domain, `π ≠ 0`, `n ≥ 1`, the homomorphism `U⁽ⁿ⁾ → O/(π)`, `1 + π^n a ↦ a mod π`; its kernel is `U⁽ⁿ⁺¹⁾`, and it is surjective in a DVR.
- `higherUnitGradedPieceMulEquivResidue` and `higher_unit_graded_equiv`: `U⁽ⁿ⁾/U⁽ⁿ⁺¹⁾ ≅ O/(π)` for `n ≥ 1` in a DVR, multiplicatively (target `Multiplicative (O/(π))`) and additively.

## Proof

Surjectivity of unit reduction comes from the quotient map being local, since `π^n O` lies in the Jacobson radical for `n ≥ 1`. The graded-piece isomorphism is the first isomorphism theorem for the coefficient map, which is a homomorphism because `(1 + π^n a)(1 + π^n b) = 1 + π^n(a + b + π^n ab)`.

## Points to watch

- `higherUnitSubgroup` is defined for an arbitrary element `π` of an arbitrary commutative ring; the unconditional isomorphisms `units_quotient_equiv` and `higher_unit_graded_equiv` are stated for a DVR with `π` irreducible and `n ≥ 1`.
- `𝔪^n/𝔪^(n+1)` in `residue_addEquiv_…` is the image of `𝔪^n` in `O/𝔪^(n+1)`, and the equivalence is only additive.
- `unitsModPowerIdealEquivOfSurjective` and `unitsModMaximalIdealPowEquivOfSurjectiveNormalized` take surjectivity of unit reduction as a hypothesis; the later versions discharge it.
- The coefficient map uses a chosen coefficient `chosenHigherUnitCoeff`, proved unique (`higherUnit_coeff_unique`) only for a domain with `π ≠ 0`.
- `units_reduction_kernel`, `higher_unit_coeff_kernel` and the like restate earlier results under other names.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/AbsoluteValue/Theory/Core.lean`: the Lean file is the source byte for byte (SHA-256 `700678fb1989465aa48d94b668ed666158b4df9aa07f8d7ed90669fdde35b987`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
