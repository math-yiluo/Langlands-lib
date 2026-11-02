# Existing FML normalization on Laurent series

Worker 27 constructs the normalization adapter for `LaurentSeries k`, for arbitrary `[Field k] [Finite k]`, by importing `Langlands.LocalField.LaurentSeries`. The module uses exactly that fixture's explicit `Langlands.LocalField.Laurent.valuativeRel k` and the existing `Langlands.FML.ord`, `normalizedMultiplicativeValuation`, and `Langlands.LocalField.residueNormalizedAbsoluteValue`. It introduces no new order, absolute value, topology, or uniform structure. To use the formulas, a consumer installs `letI := Langlands.LocalField.Laurent.valuativeRel k`, as in the core module.

## The variable and its order

`ord_single_one` proves that the usual Laurent monomial `HahnSeries.single (1 : ℤ) (1 : k)` has FML order one. This is a comparison with the existing order, not a redefinition. First, strict compatibility with Mathlib's X-adic valuation gives strictly positive FML order because the monomial has X-adic value `WithZero.exp (-1) < 1`. FML order surjectivity supplies a nonzero element `π` of order one. Its X-adic value is below one, and discreteness of `ℤᵐ⁰`, through `WithZero.lt_mul_exp_iff_le`, puts that value at most `exp(-1)`. Reversing valuation comparison by `FML.ord_le_ord_iff` bounds the monomial's FML order by one. A finite positive integer bounded by one equals one; the infinite-order case is excluded by the bound. `ord_X` transfers this result to the usual inclusion of `PowerSeries.X` using Mathlib's `HahnSeries.ofPowerSeries_X`.

`XInIntegers` is the image of `PowerSeries.X` under the actual `powerSeriesEquivIntegers` ring equivalence. Its coercion is precisely the ordinary Laurent variable. `ord_XInIntegers` gives order one for this actual integral element, `XInIntegers_mem_maximalIdeal` puts it in the actual maximal ideal by the published positive-order criterion, and `residue_XInIntegers` proves its reduction is zero by injectivity of the actual residue equivalence and the constant-coefficient calculation. Here “uniformizer” means this actual integral element has normalized additive order one; the module does not choose a different element in place of `X`.

## Integer monomials and residue-normalized absolute value

`normalizedValuation_single_one` applies the published nonzero order formula to the order-one result, obtaining logarithm minus one and hence normalized multiplicative value `exp(-1)`. Mathlib's `RatFunc.single_zpow` (despite its namespace, a theorem about Laurent monomials) expresses `single n 1` as the integer power of `single 1 1`. Valuation multiplicativity and `WithZero.exp_zsmul` then give

- `normalizedValuation_single`: `v(single n 1) = exp(-n)` for every `n : ℤ`;
- `ord_single`: `FML.ord (LaurentSeries k) (single n 1) = n` in `WithTop ℤ`;
- `ord_X_zpow`: the same order formula for `X ^ n`.

These formulas cover negative as well as positive exponents. `ord_zero` retains the established convention that the order of zero is infinity.

`residueNormalizedAbsoluteValue_single` applies the published `residueNormalizedAbsoluteValue_of_ord_eq` theorem and the core's identification `residueCardinality_eq`. Thus the actual residue-normalized absolute value is `(Nat.card k : ℝ) ^ (-n)`. `residueNormalizedAbsoluteValue_X` specializes to `(Nat.card k : ℝ)⁻¹`, and `residueNormalizedAbsoluteValue_X_zpow` supplies the all-integer-powers version. The multiplicative sign and additive sign agree: positive powers of `X` have positive order and small absolute value; negative powers have negative order and large absolute value. The core's auxiliary base-two rank-one embedding is not used to define these absolute values.

## A concrete fixture in residue characteristic two

`ZModTwo.carrier` is `LaurentSeries (ZMod 2)`. `ZModTwo.localField` discharges its local-field class through the constructed instances; Mathlib supplies the finite-field structure on `ZMod 2`, using the proved primality of two. No local-field, compactness, or residue-field hypothesis is supplied by a caller. The actual residue cardinality is two. The named formulas give order one and absolute value `1 / 2` for `X`, and order minus one and absolute value two for `X⁻¹`.

## Provenance and limits

This is a derived comparison unit built from the pinned Mathlib Laurent-series and integer-value-group constructions and the published general FML and residue-normalization interfaces. The core fixture is imported by Lean module name. The FML and residue-normalization implementations and their original attributions are retained in those imported modules; no external source or peer draft is copied here. The proof route above describes this implementation, rather than attributing these Lean-specific adapters to a numbered source theorem. This module supplies a fixture and calculations, not a classification, building, or parahoric construction. The common canonical p-adic/Laurent consumer is a separate adapter module.
