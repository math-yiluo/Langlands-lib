# Inertia and residue automorphisms for extensions of discrete valuation rings

Module `FontaineWintenberger.Ramification.Lower.Inertia`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

The file relates the zero lower ramification group of a finite group `G` acting on a local ring `S` over `R` to the ramification index and to the automorphisms of the residue field extension. It then applies this to the full Galois group of a finite Galois extension `L/K` of a complete discretely valued field, acting on the spectral integer ring.

## Main definitions and results

- `hasSeparableResidueFieldsAt_maximalIdeal`: for discrete valuation rings `R ⊆ S` with `S` finite over `R`, the map local, and the residue field of `R` perfect, Mathlib's condition `Algebra.HasSeparableResidueFieldsAt R S` holds at the maximal ideal of `R`.
- `card_lowerRamificationGroup_zero`: for such `R`, `S` with a finite group `G` such that `IsGaloisGroup G R S`, and separable residue fields at the maximal ideal, the order of `lowerRamificationGroup G (maximalIdeal S) 0` equals the ramification index of the maximal ideal of `S` over `R`.
- `localResidueGaloisHom`: for local rings `R`, `S` with a local algebra map and `IsGaloisGroup G R S`, the homomorphism from `G` to the automorphisms of the residue field of `S` over that of `R`; `localResidueGaloisHom_residue` gives its formula on residue classes.
- `localResidueGaloisHom_surjective` (for finite `G`) and `ker_localResidueGaloisHom`: the homomorphism is onto, and its kernel is the zero lower ramification group.
- `localResidueGaloisEquiv`: the resulting isomorphism from `G` modulo the zero lower group onto the residue automorphism group.
- `localResidue_normal`: the residue field extension is normal.
- For `K` a complete discretely valued field and `L/K` finite Galois: the instance `spectralIntegerRing_isGaloisGroup` says that `L ≃ₐ[K] L` acting on `spectralIntegerRing K L` has `𝒪[K]` as fixed ring. If the residue field of `K` is perfect, `spectralIntegerRing_residue_isGalois` says the residue extension is Galois, and `spectralIntegerRing_card_lower_zero` that the zero lower group has order the ramification index.

## Proofs

The order of inertia comes from Mathlib's theorem on the inertia group of a prime (`Ideal.card_inertia_eq_ramificationIdxIn`), after identifying the zero lower group with the inertia group. Surjectivity and normality come from Mathlib's `Ideal.Quotient.stabilizerHom_surjective` and `Ideal.Quotient.normal`. The fixed ring statement uses `IsGaloisGroup.of_isFractionRing`.

## Points to watch

- `lowerRamificationGroup` is the library's own definition; the group and the ring `S` are general here, not only a Galois group and a ring of integers.
- In `card_lowerRamificationGroup_zero` the separability of the residue extension is an instance hypothesis; perfection of the residue field is used only to supply it in the spectral case.
- No finiteness of the residue field is assumed anywhere.

## References

Serre, *Local Fields*, Chapter IV.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/Ramification/Lower/Inertia.lean` (SHA-256 of the source file `b25be59285cd1af4bda9215b207bfbd6003ca4bbf32062c823f2ed9bb0dc5d94`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
