# The field of norms as a valued field

Module `FontaineWintenberger.FieldOfNorms.Basic.Ring`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` satisfy `IsPerfectResidueLocalField K`, with residue characteristic `p`, and let `L/K` be a separable APF extension. The file shows that the addition `FieldOfNorms.add`, together with the multiplication already present, makes `FieldOfNorms K L` a commutative semiring, and, when `L/K` is infinite, a field of characteristic `p` with a valuation valued in `ℤ`. This is Wintenberger's Theorem 2.1.3 (ii).

## Definitions and instances

- `FieldOfNorms.instAddCommMonoid`, `FieldOfNorms.instCommSemiring` (low priority): the additive monoid and semiring structures, for `L/K` APF.
- `FieldOfNorms.instNeg`: negation, defined as `−α = (p − 1) • α`.
- `FieldOfNorms.instField`, `FieldOfNorms.instCharP`: the field structure and characteristic `p`, for `L/K` APF and infinite.
- `FieldOfNorms.fieldValuation`: the map `FieldOfNorms.valuation` bundled as a `Valuation` with values in `WithZero (Multiplicative ℤ)`; `FieldOfNorms.instValued` is the resulting `Valued` instance.

## Results

- `FieldOfNorms.add_assoc`: associativity of the addition.
- `FieldOfNorms.valuation_sum_le_one`: a finite sum of elements of valuation at most `1` has valuation at most `1`.
- `FieldOfNorms.coord_sum_sub_mem`, `FieldOfNorms.coord_nsmul_sub_mem`: for every `n`, the coordinate at `E` of a finite sum (or of `m • α`) differs from the sum of the coordinates by an element of `𝔪_E ^ n`, for all finite `E` above some finite field.
- `FieldOfNorms.natCast_prime_eq_zero`: `(p : FieldOfNorms K L) = 0` when `L/K` is infinite; hence `FieldOfNorms.pred_nsmul_add_eq_zero`: `(p − 1) • α + α = 0`.
- `FieldOfNorms.valuation_add_le_max`: the valuation of `α + β` is at most the maximum of the valuations.
- `FieldOfNorms.coord_sub_sub_mem`: the analogous approximation for differences.
- `FieldOfNorms.valuation_sub_eq_of_cofinal_coordinate`: if for cofinally many finite `E` the normalized valuation of `coord E α − coord E β` equals `exp (−n)`, then the valuation of `α − β` is `exp (−n)`.
- `FieldOfNorms.field_add`, `FieldOfNorms.field_toCommSemiring`, `FieldOfNorms.field_toCommGroupWithZero`: the field addition is `FieldOfNorms.add`, and the field structure restricts to the earlier semiring and group-with-zero structures by definitional equality.

## Proofs

Ring identities are proved by showing that both sides have coordinates agreeing modulo every power of the maximal ideal on a tail (`FieldOfNorms.add_sub_mem`) and then applying the separation result `FieldOfNorms.ext_of_eventually_sub_mem`. The vanishing of `p` uses that `p` lies in arbitrarily high powers of the maximal ideals of large finite layers, which rests on unbounded ramification in an infinite APF extension. The ultrametric inequality reduces to the integral case by scaling.

## Points to watch

- The field structure, negation, characteristic and `Valued` instance require infiniteness, as an instance `Fact (¬ Module.Finite K L)`. The semiring exists for every separable APF extension.
- Only part (ii) of Theorem 2.1.3 is attributed here; completeness and the residue field are not in this file.
## References

Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §§2–3, Theorem 2.1.3 (ii).

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/FieldOfNorms/Basic/Ring.lean` (SHA-256 of the source file `161a46cd094c0a43f8623ccf5537d001c4a93c03bec9b2aff4267add57289dd7`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
