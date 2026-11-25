# The coefficient field of a truncated local ring of characteristic p

Module `FontaineWintenberger.Ramification.Lower.TruncatedCoefficients`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `R` be a local ring of characteristic `p` whose maximal ideal is nilpotent and whose residue field is perfect. The file shows that the Teichmüller section of the residue map, constructed in the file on multiplicative representatives, is then additive, hence a ring homomorphism from the residue field to `R`: a canonical copy of the residue field inside `R`.

## Main definitions and results

- `isAdicComplete_of_isNilpotent_ideal`: a commutative ring is adically complete for any nilpotent ideal.
- `residueTeichmuller_eq_pow_of_nilpotent`: if the `h`-th power of the maximal ideal is zero and `h ≤ p ^ n`, then for any `b` in `R` lifting the `p^n`-th root of `x` (written as the `n`-th coordinate of `x` in the perfection of the residue field), `residueTeichmuller R p x = b ^ p ^ n` exactly.
- `residueTeichmuller_add_of_isNilpotent`: when the maximal ideal is nilpotent, `residueTeichmuller R p` is additive.
- `truncatedResidueCoefficients R p hI`: the resulting ring homomorphism from the residue field to `R`, for `hI : IsNilpotent (maximalIdeal R)`. Its multiplicative part is `residueTeichmuller R p` (`truncatedResidueCoefficients_eq_residueTeichmuller`).
- `residue_truncatedResidueCoefficients`, `residue_comp_truncatedResidueCoefficients`: it is a section of the residue map.
- `truncatedResidueCoefficients_unique`: it is the only ring homomorphism from the residue field to `R` that is a section of the residue map.
- `truncatedResidueCoefficients_eq_pow`: the formula `b ^ p ^ n` above, for this section.
- `truncated_residue_pow_independent`: the value `a ^ p ^ n` does not depend on the exponent `n` with `h ≤ p ^ n`, nor on the lift.
- `truncatedResidueCoefficients_naturality`, `truncatedResidueCoefficients_naturality_comp`: a local ring homomorphism `f : R → S` between two such rings commutes with the coefficient sections and the induced map of residue fields.

## Proofs

For the exact formula, the difference between the Teichmüller representative of the `p^n`-th root and `b` lies in the maximal ideal, so its `p^n`-th power vanishes; in characteristic `p` the `p^n`-th power of a difference is the difference of the powers. Additivity follows by the same identity for sums, taking `n = h`. Uniqueness and naturality are those of `residueTeichmuller`.

## Points to watch

- `R` itself has characteristic `p` (`CharP R p`), in addition to its residue field: this is the equal-characteristic, truncated situation, for instance a quotient of a ring of integers by an ideal containing `p`. In mixed characteristic the Teichmüller map is not additive.
- Nilpotence of the maximal ideal is an explicit argument `hI` of the definition, not an instance; completeness is derived from it.
- The roots of `x` are phrased through Mathlib's `Perfection.coeff` and `PerfectionMap.id`.
- The residue field need not be finite.

## References

Serre, *Local Fields*, Chapter IV.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/Ramification/Lower/TruncatedCoefficients.lean` (SHA-256 of the source file `723ef89312f83d0c50ea3515d32829f84c9fe40fd3130ae845528493c244158f`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
