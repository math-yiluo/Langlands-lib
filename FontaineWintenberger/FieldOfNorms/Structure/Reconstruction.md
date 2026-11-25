# Reconstructing norm families from the truncated norm tower

Module `FontaineWintenberger.FieldOfNorms.Structure.Reconstruction`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `L/K` be an infinite APF extension of a field `K` with `IsPerfectResidueLocalField K`, `D` a finite intermediate field, `𝔈 = deepFiniteTower K L D` and `𝔅 n = DeepFiniteTowerQuotient K L D n`. The file shows that every compatible family of classes in the quotients `𝔅 n` comes from a unique integral element of the field of norms.

## Main definitions

- `deepNormInverseLimit K L D` (written `𝒜`): the subring of compatible families in `∏ 𝔅 n` for the transitions `deepFiniteTowerTransition n (n+1)`, an instance of `SequentialInverseLimit.subring`.
- `deepNormRepresentative a n`: a chosen integer of `𝔈 n` whose class is the `n`-th coordinate of `a`.
- `deepNormSequence x j n`: for integers `x n ∈ 𝔈 n`, the norm of `x n` down to `𝔈 j` when `j ≤ n`, and `x j` otherwise.
- `deepNormCoordinate a j`: the limit in `𝔈 j` of the norm sequence of the chosen representatives.
- `deepNormFamily a F`: for a finite intermediate field `F`, the norm of `deepNormCoordinate a j` from a stage `𝔈 j ⊇ F`.
- `deepNormReconstruction a`: the resulting element of `FieldOfNorms K L`.

## Main results

- `deepNormRepresentative_norm_sub_mem`: for any representatives `x`, the norm of `x m` to `𝔈 n` is congruent to `x n` modulo `𝔪^(n+2)`.
- `deepNormSequence_cauchy`, `exists_tendsto_deepNormSequence`: the norm sequence of any representatives is Cauchy, hence convergent, in each `𝔈 j`.
- `deepNormCoordinate_mem`, `deepNormCoordinate_norm`, `deepNormCoordinate_sub_mem`: the limits are integral, norm-compatible, and congruent to the representative modulo `𝔪^(j+2)`.
- `deepNormFamily_eq_norm`, `deepNormFamily_norm`, `deepNormFamily_mem`: the family on all finite subfields is independent of the stage used, norm-compatible and integral.
- `existsUnique_fieldOfNorms_deepNormCoordinate`: exactly one `γ` of valuation `≤ 1` has coordinates `deepNormCoordinate a j` at every `𝔈 j`.
- `deepNormSequence_tendsto`, `deepNormReconstruction_tendsto`: the limit does not depend on the representatives.
- `deepNormReconstruction_sub_mem_of_representative`: the coordinate of the reconstruction at `𝔈 j` is congruent modulo `𝔪^(j+2)` to any representative.
- `existsUnique_fieldOfNorms_of_truncatedNorms`: exactly one integral `γ` has, for all representatives and all `j`, the norm sequence converging to its coordinate at `𝔈 j`.

## Proofs

The Cauchy property uses `integerNorm_sub_congruence_of_totallyRamified` for the totally ramified `p`-power steps of the tower, with `le_ceil_apfPhi_of_apfPsi_le` to turn precision `n+2` at stage `n` into precision `N` at stage `j`. Limits exist because finite extensions of `K` are complete. The element of the field of norms comes from `existsUnique_fieldOfNorms_of_compatible`.

## Points to watch

- Representatives, limits and indices are obtained by `choose`; the uniqueness statements make the construction canonical.

## References

Wintenberger, *Le corps des normes de certaines extensions infinies de corps locaux; applications*, §2–3.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/FieldOfNorms/Structure/Reconstruction.lean` (SHA-256 of the source file `f4dfec948dc28aac8462de972881bd1affb14203f71111bddbda093caa25f82c`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
