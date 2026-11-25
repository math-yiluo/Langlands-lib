# Upper ramification groups and upper jumps of finite extensions of local fields

Module `Nyll.ValuedFieldTheory.Ramification.LocalField.Core`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a nonarchimedean local field `K` and a finite Galois extension `L/K`, the file defines the real-indexed lower and upper ramification groups of `Gal(L/K)`, the right limit of the upper filtration, and the predicate "t is an upper jump". It shows that upper numbering is compatible with passing to Galois subextensions and locates the possible jumps.

## Definitions

- `chosenLocalExtensionCompleteDVF_hasUniqueDVFValuationExtension`: for `L/K` finite separable, the complete discrete valuation chosen on `L` is the unique extension of the canonical one on `K`, in the form the ramification API needs.
- `localLowerRamificationGroup K L t` and `localUpperRamificationGroup K L t` (`t : ℝ`): the lower group `G_t` and the upper group `G^t = G_s` for `s = ψ(t)`, with `ψ` the inverse Herbrand function, computed with the valuation chosen on `L`.
- `localUpperRamificationGroupAfter K L t`: the supremum of the `G^s` over `s > t`.
- `IsLocalUpperRamificationJump K L t`: `G^t` differs from this right limit.

## Main results

- `localUpperRamificationGroup_map_autCongr`: a `K`-algebra isomorphism `L ≃ M` carries `G^t(L/K)` onto `G^t(M/K)`.
- `localUpperRamificationGroup_map_restrict`: for finite Galois subextensions `E ≤ F` of the separable closure of `K`, restriction `Gal(F/K) → Gal(E/K)` maps `G^t(F/K)` onto `G^t(E/K)`. The analogue for right limits is `localUpperRamificationGroupAfter_map_restrict`, and `isLocalUpperRamificationJump_of_map_restrict` deduces that every upper jump of `E` is an upper jump of `F`.
- `localUpperRamificationGroup_antitone`: `G^t` decreases as `t` grows. `localUpperRamificationGroupAfter_le`: the right limit at `t` lies in `G^t`.
- For `t ≤ 0` the upper and lower groups agree. Both filtrations are constant on `(-1, 0]`, and `G^t` is all of `Gal(L/K)` for `t ≤ -1`.
- `isLocalUpperRamificationJump_eq_neg_one_or_nonneg`: every upper jump is `-1` or nonnegative. It rests on the absence of jumps below `-1` and strictly between `-1` and `0`.

## Proofs

The restriction theorem identifies `Gal(E/K)` with a quotient of `Gal(F/K)` by a fixing subgroup. It then applies the quotient theorem for upper groups from the imported Herbrand-theorem file and transports along field isomorphisms. The transport step compares lower groups and Herbrand functions through a ring isomorphism of valuation rings.

## Points to watch

- The groups are built from the library's own complete discrete valuation fields and lower filtration, not from Mathlib's. The valuation on `L` is a chosen one, justified by the uniqueness of the extension.
- The proofs show that the lower group at a real index `t` is cut out by the maximal ideal raised to `realRamificationExponent t`, that is to `max(0, ⌈t + 1⌉)`. Hence `-1` is a possible jump, and the upper group there is the whole Galois group.
- The restriction results are stated only for subfields of `SeparableClosure K` that are finite and Galois over `K`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Ramification/LocalField/Core.lean`: the Lean file is the source byte for byte (SHA-256 `0a5463131f5fd9b349428a68bf95accb71f6d13b06bee22f6236541c9f9f73b1`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
