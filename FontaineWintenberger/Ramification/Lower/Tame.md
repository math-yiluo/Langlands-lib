# The tame inertia homomorphism

Module `FontaineWintenberger.Ramification.Lower.Tame`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `B` be a discrete valuation ring with a group `G` acting by ring automorphisms. For a uniformizer `π` and `g` in `G`, the element `g • π` is again a uniformizer, hence `π` times a unit. The file studies the residue class of this unit on the inertia group, and proves that the quotient of inertia by wild inertia is cyclic of order prime to the residue characteristic.

## Main definitions and results

- `uniformizerRatio G hπ g`: a unit `u` of `B` with `π * u = g • π` (`mul_uniformizerRatio`). It satisfies the cocycle rule `u(gh) = u(g) * g • u(h)` (`coe_uniformizerRatio_mul`).
- `residue_smul_eq_of_mem_lower_zero`: an element of `lowerRamificationGroup G (maximalIdeal B) 0` fixes every residue class.
- `tameInertiaHom G hπ`: the homomorphism from the zero lower ramification group to the units of the residue field of `B`, sending `g` to the residue class of `uniformizerRatio G hπ g`.
- `tameInertiaHom_eq`: this homomorphism does not depend on the uniformizer.
- `ker_tameInertiaHom`: if the residue field is perfect of characteristic `p`, the kernel is the first lower ramification group, seen inside the zero one.
- `tameInertiaQuotientEquiv`: under the same hypotheses, the quotient of the zero lower group by the first is isomorphic to the image of `tameInertiaHom`.
- `isCyclic_tameInertiaQuotient`: if moreover `G` is finite, this quotient is cyclic.
- `coprime_card_tameInertiaQuotient`: its order is prime to `p`.

## Proofs

The kernel is computed with the criterion `mem_lowerRamificationGroup_iff_uniformizer` of the file on uniformizers: an element of inertia lies in the first lower group exactly when `g • π - π` lies in the square of the maximal ideal; since `g • π - π = π * (u - 1)`, this says that `u` reduces to 1. Cyclicity holds because the quotient embeds as a finite subgroup of the units of a field. For the order, an element of order `p` in the quotient would map to a `p`-th root of unity in a field of characteristic `p`, which is 1 by injectivity of Frobenius.

## Points to watch

- `uniformizerRatio` is chosen by `Classical.choose`; it is determined by `mul_uniformizerRatio` since `π ≠ 0`.
- The residue field is not assumed finite. The hypotheses of perfect residue field and characteristic `p` enter through the criterion on uniformizers; the definition of `tameInertiaHom` and its independence of `π` need neither.
- The case of residue characteristic zero is not covered by the kernel statement, which requires a prime `p`.
- The ring `B` is not assumed complete, and `G` is an arbitrary group acting on `B`; finiteness of `G` is used only for the last two theorems.

## References

Serre, *Local Fields*, Chapter IV.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/Ramification/Lower/Tame.lean` (SHA-256 of the source file `2833a83c9fd0d37b72fa2a003854dc4c99bac4cd004ebe1ff3b68ca8d1258c4e`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
