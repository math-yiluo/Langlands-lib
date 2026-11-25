# The closed unit ball of a nonarchimedean absolute value

Module `Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.ValuationSubring`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a real absolute value `v` on a field `K` that is nonarchimedean (in the library's sense of being bounded on the integers), the file builds the closed unit ball `{x | v x ≤ 1}` as a subring and as a Mathlib `ValuationSubring`, and describes its units, maximal ideal, residue map, integral closedness, behaviour under extension of absolute values, and lifts of polynomials with coefficients in the ball. This is the valuation ring used later for the norm construction in finite extensions.

## Main definitions and results

- `absoluteValueUnitBallSubring v hnonarch`: the subring `{x | v x ≤ 1}`; `absoluteValueValuationSubring v hnonarch`: the same set as a `ValuationSubring K`, since `x` or `x⁻¹` lies in it.
- `isUnit_iff_abs_eq_one_of_mem_iff_le_one`: in any submonoid whose members are exactly the elements with `v x ≤ 1`, the units are the elements with `v x = 1` and the nonunits those with `v x < 1`; specialized to the valuation subring.
- `absoluteValueValuationSubring_mem_maximalIdeal_iff_abs_lt_one`: the maximal ideal is the open unit ball; the residue of `x` is zero exactly when `v x < 1`, and nonzero exactly when `v x = 1`.
- `absoluteValueUnitBallSubring_isIntegrallyClosedIn`: the ball is integrally closed in `K`.
- `comap_absoluteValueUnitBallSubring_eq_of_extends`: if `w` on `L ⊇ K` restricts to `v`, the ball of `w` pulls back to the ball of `v`; that `w` is nonarchimedean is a separate hypothesis (`hwnonarch`), not derived from `v`.
- `polynomial_lifts_absoluteValueUnitBallSubring_iff_coeff_mem`: `f ∈ K[X]` comes from the ball exactly when its coefficients lie in it. A monic such `f` lifts to a monic polynomial of the same degree, and any `f` with `v` of all coefficients at most `1` lifts to the valuation subring with the same degree and coefficient values.

## Points to watch

- Nonarchimedean means the library's predicate `LubinTate.Valuations.NonarchimedeanAbsoluteValue` (boundedness on `ℕ`); the strong triangle inequality used for closure under addition comes from the library's equivalence between the two.
- Two bundlings of the same set appear, a `Subring` and a `ValuationSubring`; statements switch between them.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/AbsoluteValue/ValuationSubring.lean`: the Lean file is the source byte for byte (SHA-256 `78626e0984773833977519d6b252d8863b9f4f65278603a0e05fefbb923dd641`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
