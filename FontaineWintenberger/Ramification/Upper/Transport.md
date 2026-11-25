# Transport of ramification data, and upper groups under restriction

Module `FontaineWintenberger.Ramification.Upper.Transport`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

The file shows that ramification orders, lower groups, Herbrand functions and upper groups are unchanged when the acting group or the discrete valuation ring is replaced by an isomorphic one. It uses this to state Herbrand's theorem for upper groups with ordinary restriction of automorphisms between finite Galois extensions of a complete discretely valued field `K`.

## Main definitions and results

Relabelling the group: for an isomorphism `e : G ≃* G'` of groups acting on the same discrete valuation ring `R` with `e g • a = g • a`, the lemmas `ramificationOrder_mulEquiv`, `lowerRamificationGroup_map_mulEquiv`, `lowerRamificationGroupReal_map_mulEquiv`, `herbrandFunction_mulEquiv`, `inverseHerbrandFunction_mulEquiv`, `upperRamificationGroup_map_mulEquiv` say that `e` carries each object for `G` to that for `G'`.

Changing the ring: `addVal_ringEquiv` says a ring isomorphism of discrete valuation rings preserves the valuation. For `r : R ≃+* S` and `e : G ≃* G'` with `r (g • a) = e g • r a`, the lemmas `ramificationOrder_equivariant`, `lowerRamificationGroupReal_map_equivariant`, `herbrandFunction_equivariant`, `inverseHerbrandFunction_equivariant`, `upperRamificationGroup_map_equivariant` give the same conclusions.

Field isomorphisms: for algebraic extensions `L`, `M` of `K` and `f : L ≃ₐ[K] M`,

- `spectralIntegerRingEquiv K f`: the induced isomorphism of spectral integer rings over `𝒪[K]`, with `coe_spectralIntegerRingEquiv` and the equivariance `spectralIntegerRingEquiv_smul` for conjugation `f.autCongr`.
- `ramificationOrder_autCongr`, `herbrandFunction_autCongr`, `upperRamificationGroup_map_autCongr`: for `L`, `M` finite separable, conjugation by `f` preserves orders, Herbrand functions and upper groups.

Restriction, for `L/K` finite Galois:

- `restrictNormal_mem_intermediate_decomposition`, `intermediateDecompositionRestriction`: restriction to an intermediate field `F` Galois over `K`, as a map into the decomposition subgroup of the valuation ring of `F`.
- `intermediate_map_upperRamificationGroup`, `restrictNormalHom_map_upperRamificationGroup`: if the residue field of `K` is perfect and `u ≥ -1`, restriction maps the upper group at `u` of `L ≃ₐ[K] L` onto that of `F`, the second with `F ≃ₐ[K] F` acting on `spectralIntegerRing K F`.
- `restrictNormalHom_map_upperRamificationGroup_tower`: the same for a tower `K ⊆ F ⊆ L` of finite Galois extensions given as separate fields.
- `finGaloisGroupMap_map_upperRamificationGroup`: Mathlib's transition maps `finGaloisGroupMap` between Galois groups of finite Galois intermediate fields of an extension `Ω/K` preserve upper groups.

## Proofs

Each transport lemma reduces to equality of ramification orders. The restriction theorems reduce to `fixedField_map_upperRamificationGroup`, by writing `F` as the fixed field of its fixing subgroup and identifying the restricted valuation ring with the spectral integer ring of `F`.

## Points to watch

- Statements on inverse Herbrand functions and upper groups require `u ≥ -1` and finite groups.
- The restriction theorems assume a perfect residue field.
- In the last theorem `Ω/K` is an arbitrary field extension.

## References

Serre, *Local Fields*, Chapter IV.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/Ramification/Upper/Transport.lean` (SHA-256 of the source file `8982e0b64d5cf212f9a48866910c2e7fbafbe2307dc2c9720b2e5db490ec2153`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
