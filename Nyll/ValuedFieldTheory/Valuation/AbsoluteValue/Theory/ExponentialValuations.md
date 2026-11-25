# Exponential valuations, their valuation rings and discrete valuation rings

Module `Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.Theory.ExponentialValuations`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file introduces additive ("exponential") valuations `v : K → ℝ ∪ {∞}` on a field, their equivalence under scaling, the absolute values `|x| = q^(−v(x))`, and their valuation rings, which for discrete valuations are shown to be discrete valuation rings.

## Definitions

- `ExponentialValuation K`: a map `K → WithTop ℝ` with `v x = ∞ ↔ x = 0`, `v(xy) = v x + v y` and `min(v x, v y) ≤ v(x + y)`.
- `EquivalentExponentialValuations v w`: `v = s·w` on nonzero elements for some `s > 0`.
- `AssociatedAbsoluteValue v q abv`: `q > 1` and `abv x = q^(−v(x))` for `x ≠ 0` (a relation, not a construction).
- `exponentialValuationSubring v` (`v ≥ 0`), also bundled as a Mathlib `ValuationSubring`; `exponentialUnitSet` (`v = 0`), `exponentialMaxIdealSet` and the ideal `exponentialMaxIdeal` (`v > 0`).
- `DiscreteExponentialValuation v`: for some `s > 0` all finite values lie in `sℤ` and `s` is attained. `NormalizedExponentialValuation v`: discrete, integer-valued, with an element of value `1`. `PrimeElementFor v π`: `π ≠ 0` and `v π = 1`.
- `uniformizerPowerIdeal π n`: the ideal `(π^n)` in any commutative ring.

## Main results

- The valuation ring is a local ring whose maximal ideal is `exponentialMaxIdeal v` and whose units are the elements of value `0`.
- Equivalent valuations have the same ring, units and maximal ideal. For an associated absolute value, ring, units and maximal ideal are the closed unit ball, the unit sphere and the open unit ball.
- For a normalized valuation and a prime element `π`: every `x ≠ 0` is uniquely `u·π^m` with `u` a unit (`normalizedExponentialValuation_exists_unique_unit_mul_zpow`); `𝔪 = (π)`, `π` is prime and irreducible, and `𝔪^n = (π^n)`; `x ∈ (π^n)` iff `v x ≥ n`; every nonzero ideal is some `(π^n)` (`nonzero_ideal_eq_uniformizerPowerIdeal`); the ring is a PID and a DVR.
- `discreteExponentialValuationSubring_isPrincipalIdealRing` and `…_isDiscreteValuationRing`: the same for a discrete valuation with arbitrary positive generator `s`, with membership in `(π^n)` given by `v x ≥ n s`.

## Proof

The ideal classification picks an element of least value `n s` in a nonzero ideal and shows the ideal is `(π^n)`, since elements of value exactly `n s` are unit multiples of `π^n`.

## Points to watch

- `ExponentialValuation` is the library's own structure, not Mathlib's `Valuation` or `AddValuation`; it is real-valued with `+∞` at `0`.
- `NormalizedExponentialValuation` is stated through integer values and an element of value `1`, not through surjectivity onto `ℤ ∪ {∞}`.
- `discretePrimeElementInValuationSubring` only requires a nonnegative value (value `0` is allowed despite the name).

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/AbsoluteValue/Theory/ExponentialValuations.lean`: the Lean file is the source byte for byte (SHA-256 `6020980635be7ac886b63cd69d5428302ae49169a20ef128cfe00d61db6aca60`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
