# Degree, ramification index and residue degree for extensions of discrete valuation rings

Module `FontaineWintenberger.Ramification.Lower.Degree`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

For a finite injective local homomorphism `R → S` of discrete valuation rings, the file proves the identity `e · f = n` and its consequence that, in the totally ramified case, every uniformizer of `S` generates `S` over `R`. The ramification index and inertia degree are Mathlib's `Ideal.ramificationIdx` and `Ideal.inertiaDeg` for the maximal ideals.

## Results

For discrete valuation rings `R`, `S` with `S` a finite `R`-algebra, the structure map injective and local:

- `local_inertiaDeg_eq_finrank_residueField`: the inertia degree of the maximal ideal of `S` over `R` is the degree of the residue field extension.
- `local_ramificationIdx_mul_inertiaDeg`, `local_ramificationIdx_mul_finrank_residueField`: `e · f = Module.finrank R S`.
- `ramificationIdx_eq_finrank_iff_residue_surjective`: `e = Module.finrank R S` if and only if the map of residue fields is surjective.
- `adjoin_uniformizer_eq_top_of_ramificationIdx_eq_finrank`: if `e = Module.finrank R S`, then `Algebra.adjoin R {π} = ⊤` for every uniformizer `π` of `S`.
- `local_ramificationIdx_mul_residueDegree_eq_finrank`, `adjoin_uniformizer_eq_top_of_ramificationIdx_eq_field_finrank`: the same two statements with `Module.finrank K L` for the fraction fields `K`, `L`.

For `K` a complete discretely valued field in the library's sense, `L/K` finite separable and `w` a valuation on `L` extending that of `K`:

- `extensionValuationSubring_ramificationIdx_mul_residueDegree`: `e · f = [L : K]` for the valuation ring of `w` over `𝒪[K]`.
- `extensionValuationSubring_adjoin_uniformizer_eq_top`: if `e = [L : K]`, every uniformizer generates the valuation ring of `w` over `𝒪[K]`.

For `K` a field with a `Valued K ΓK` structure that is rank-one discrete, complete, with valuation ring a discrete valuation ring, and `L`, `w` as above:

- `discreteValued_extension_moduleFinite`: the valuation ring of `w` is finite over that of `K`.
- `discreteValued_extension_ramificationIdx_mul_residueDegree`, `discreteValued_extension_adjoin_uniformizer_eq_top`: the same two statements in this setting.

## Proofs

The identity `e · f = n` is Mathlib's formula `Σ e_i f_i = n` (`Ideal.sum_ramification_inertia_eq_finrank`), in which only the maximal ideal of `S` lies over that of `R`. The generation statement rests on `adjoin_uniformizer_eq_top`, proved elsewhere in the library, which needs surjectivity on residue fields. The statements for `Valued` fields are transported from the normed setting through private local instances.

## What to watch for

- "Totally ramified" is expressed by the equality of `e` with the degree; no separability of the residue extension is assumed.
- The extension of valuation rings in the last two groups is assumed separable on fraction fields, and `K` is complete.
- In the `Valued` section the norm on `K` is constructed locally from the valuation with base `2`; this choice is not visible in the statements.

## References

Serre, *Local Fields*, Chapter IV.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/Ramification/Lower/Degree.lean` (SHA-256 of the source file `ba03bd5605796cb070e7add770027e5881005c0a110f9178da9cc958878778b1`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
