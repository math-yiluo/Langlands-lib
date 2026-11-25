# The changed primitive polynomial at the original primitive point

Module `Nyll.ClassFieldTheory.LubinTate.FiniteLevel.ChangedPrimitiveEvaluation`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `F` be a local field structure on `K` with residue field of cardinality `q`, `π` a uniformizer, and `u` a unit with `u − 1 ∈ m^(n+1)`; put `π' = uπ`. The file shows that the Lubin–Tate primitive polynomial of level `n` for `π'`, evaluated at the chosen primitive point of the standard level `n` for `π`, has large valuation. This is the quantitative input for a Krasner-type comparison of the original and changed levels.

## Main results

All take the hypothesis `hu` that `u` lies in the higher principal unit group of index `n + 1`. Write `d = (q − 1)·q^n`, the ramification index of the standard level `n` over `F`.

- `standardLubinTateChangedUniformizer_sub_mem_maximalIdeal_pow`: `π' − π ∈ m^(n+2)` in the valuation ring of `F`.
- `standardLubinTateChangedUniformizer_map_sub_mem_levelMaximalIdeal_pow`: in the valuation ring of the level, the images of `π'` and `π` differ by an element of the `d(n+2)`-th power of the maximal ideal.
- `standardLubinTateChangedPrimitivePolynomial_eval_mem_maximalIdeal_pow`: the changed primitive polynomial at the original primitive point lies in that power.
- `standardLubinTateChangedPrimitivePolynomial_eval_addVal_ge`: equivalently, its normalized additive valuation is at least `d(n+2)`.

## Proof

`π' − π = (u − 1)π`. Under the inclusion of valuation rings, depth is multiplied by the ramification index, which equals the degree `(q − 1)·q^n` of the level. The parameter-congruence theorem turns the congruence of parameters into a congruence of the evaluated primitive polynomials, and the original primitive polynomial vanishes at the original point.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LubinTate/FiniteLevel/ChangedPrimitiveEvaluation.lean`: the Lean file is the source byte for byte (SHA-256 `e48c4c636a349f144453e51499caeaa342b475ebe3746fb866430f1964dfbaf8`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
