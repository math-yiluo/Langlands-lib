# Wild tails of separable APF extensions

Module `FontaineWintenberger.APF.Tower.Wild`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` satisfy `IsPerfectResidueLocalField K`, with residue characteristic `p`, and let `L/K` be a separable APF extension. The file shows that beyond some finite intermediate field, every step `E ≤ F` between finite intermediate fields of `L` is "wild": the residue fields coincide, the degree is a power of `p`, and the step is totally ramified. Neither `L` nor its finite subfields are assumed normal over `K`.

## Results

Two lemmas on a finite group `G`:

- `relIndex_sup_eq_relIndex_of_normal_right`: for subgroups `A`, `U` with `U` normal, the relative index of `A` in `A ⊔ U` equals its relative index in `U` (that is, `[U : A ∩ U]`).
- `relIndex_eq_prime_pow_of_le_sup`: for a prime `q`, subgroups `A ≤ B ≤ C ≤ A ⊔ U` with `U` a normal `q`-group, the index of `B` in `C` is a power of `q`.

On fields:

- `finrank_eq_prime_pow_of_apfFiniteStage_one_le`: for intermediate fields `E ≤ F ≤ L` of the separable closure with `F` finite and `apfFiniteStage K L 1 ≤ E`, the degree `[F : E]` is a power of `p`.
- `FiniteIntermediateField.ramificationIdx_eq_finrank_of_residueInclusion_surjective`: for finite intermediate fields `E ≤ F` of a separable `L/K`, if the residue map `spectralResidueInclusion` from `E` to `F` is surjective, then the ramification index of the maximal ideal of `spectralIntegerRing K F` over `spectralIntegerRing K E` equals `[F : E]`.
- `IsAPF.exists_finiteIntermediateField_residue_surjective_and_degree_prime_pow`: for `L/K` APF there is a finite `T` such that for all finite `T ≤ E ≤ F` the residue map is surjective and `[F : E]` is a power of `p`.
- `IsAPF.exists_finiteIntermediateField_wild_tail`: the same `T`, with the further conclusion that the ramification index of `F/E` equals `[F : E]`.

## Proofs

For the degree, pass to the finite Galois normal closure `Ω` of `F`. The image of the upper ramification group `G_K^1` in `Gal(Ω/K)` is the upper ramification group of index `1`, which lies in the lower ramification group of index `1` and is therefore a `p`-group. The hypothesis on the stage puts the fixing subgroup of `E` inside the product of the image of `G_L` with this `p`-group, and the group lemma applies. Surjectivity of residue maps on a tail comes from `IsAPF.exists_finiteIntermediateField_residueInclusion_surjective`; total ramification then follows from the identity `e · f = n` for the local extension of spectral integer rings.

## Points to watch

- The tail starts above a field containing both the pull-back of the stage at parameter `1` and a residue-stable field; it is given by an existence statement, not as a canonical field.
## References

Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §1.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/APF/Tower/Wild.lean` (SHA-256 of the source file `1d7cb6322fbffeed0e8c0c2d323641b8a35252270bcd65c07cc9494213d305e5`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
