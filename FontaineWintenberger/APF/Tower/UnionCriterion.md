# An APF criterion for towers with prescribed ramification profiles

Module `FontaineWintenberger.APF.Tower.UnionCriterion`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` be a complete discretely valued field, `E n` a sequence of finite subfields of its separable closure and `b n` a sequence of reals. The file isolates the passage from finite fields to their union in Wintenberger's Remark 1.4.2. Two hypotheses on the APF products `apfSubgroup` recur:

- `hstep`: for `-1 ≤ u ≤ b n`, the products of `E (n+1)` and `E n` at `u` are equal;
- `htail`: for `u > b n`, the product of `E (n+1)` at `u` is the fixing subgroup of `E (n+1)`.

## Results

- `apfSubgroup_eq_of_step_profiles`: under `hstep` with `b` monotone, the products of `E m` and `E n` agree at every `u` with `-1 ≤ u ≤ b n`, for `n ≤ m`.
- `apfSubgroup_iSup_eq_of_step_profiles`: with `E` and `b` monotone and `hstep`, the product of the union `⨆ m, E m` at such `u` equals that of `E n`.
- `isAPF_iSup_of_step_profiles`: under the same hypotheses, if `b n → ∞` then the union is APF.
- `not_finiteDimensional_iSup_of_strictMono`: the union of a strictly increasing sequence of finite intermediate fields is infinite over `K`.
- `apfSubgroup_iSup_eq_fixingSubgroup_of_bounded`: with `E` monotone and `htail`, if `u > b n` for all `n`, the product of the union at `u` is the fixing subgroup of the union.
- `tendsto_of_isAPF_iSup_of_step_profiles`: with `E` strictly increasing, `b` monotone and `htail`, if the union is APF then `b n → ∞`.
- `isAPF_iSup_iff_tendsto_of_step_profiles`: with `E` strictly increasing, `b` monotone, `hstep` and `htail`, the union is APF if and only if `b n → ∞`.
- `apfSubgroup_iSup_eq_fixingSubgroup_of_step_profiles`: with `E`, `b` monotone, `hstep` and `htail`, for `u ≥ -1` with `b n < u ≤ b (n+1)` the product of the union at `u` is the fixing subgroup of `E (n+1)`.

## Proofs

The product of an increasing union is the intersection of the products of its members (`apfSubgroup_iSup_eq_iInf`, from the file on unions); by `hstep` this intersection stabilizes below `b n`, and openness is inherited from the finite field `E n`. Conversely, if `b` were bounded, the product of the union at a parameter above all `b n` would be the fixing subgroup of the union; APF makes it open, so the union would be finite over `K`, which a strictly increasing tower excludes.

## Points to watch

- The profile conditions `hstep` and `htail` are hypotheses; this file does not derive them from elementary steps.
- The equivalence needs `E` strictly increasing; the direction from divergence to APF needs only monotonicity.

## References

Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §1.4.2.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/APF/Tower/UnionCriterion.lean` (SHA-256 of the source file `5094c1df16b54caea35706ba61fc68fb518a2d81901a1171e9217878e0a5769d`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
