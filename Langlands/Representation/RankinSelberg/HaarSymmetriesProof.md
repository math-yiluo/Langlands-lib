# Symmetries of the normalized general linear Haar measure

Worker 51's `Langlands.RankinSelberg.generalLinearHaarSymmetries` has exactly
the type `GeneralLinearHaarSymmetriesStatement F n`. It covers every field
universe and nonarchimedean local field, every positive matrix rank `n + 1`,
and the given Borel measurable structure on the actual matrix group. It adds
no unimodularity, countability, or characteristic assumption. The final
unapplied-constant example verifies the full outer parameter telescope.

This proof is authored by Worker 51. It proves the unchanged statement already
published in the Library and preserves its normalization and full parameter
telescope.

## Implemented proof

The private helper `normalizedHaar_eq` treats a regular left Haar measure `μ`
and a regular left-invariant measure `ν` on a locally compact topological
group. Mathlib's `isMulLeftInvariant_eq_smul_of_regular` writes `ν` as a
nonnegative-real scalar times `μ`. If both measures give an actual set `K`
mass one, evaluating this equality on `K` forces the scalar to be one.
Regularity supplies finiteness on compact sets. The helper requires no
commutativity, second countability, or assumed probability measure on the
whole group.

The private `normalizedCompactOpenHaar_inv` applies this comparison to the
inverse pushforward of a compact-open-subgroup-normalized Haar measure. Its
explicit right-invariance assumption makes the inverse pushforward left
invariant. Inversion preserves regularity. The inverse of the subgroup is
itself, so both measures assign it mass one. This proves inversion invariance
without using Mathlib's abelian-group inversion-invariance instance.

For the actual general linear group, the local-field hypotheses give a
Hausdorff topology through the additive uniform structure. Finite matrix
spaces are locally compact, and their unit groups inherit local compactness.
The published `generalLinearHaar_isMulRightInvariant` supplies right
invariance of precisely the measure already defined in `Measures`. Applying
the preceding compact-open result proves the first target conjunct.

For inverse transpose, the existing `inverseTransposeContinuous` is used as
a continuous group automorphism, so its pushforward is Haar and regular.
The private `inverseTranspose_mem_integral` proves preservation of the actual
integral matrix subgroup: the map swaps forward and inverse matrices and
reverses their two entry indices. The characterization
`Conductor.mem_integralSubgroup` requires all entries of both matrices to be
integral, so these operations preserve membership in both directions. This
subgroup is open, hence measurable. Evaluating the pushforward on it gives
mass one by `generalLinearHaar_integralSubgroup`. Regular Haar uniqueness
then proves the inverse-transpose pushforward equals the original measure;
continuity supplies the measurability clause of `MeasurePreserving`.

The transpose map in the target is inverse transpose composed with inversion.
Composing the two proved measure-preserving maps proves its conjunct. For
conjugation by `a`, compose left multiplication by `a` with right
multiplication by `a⁻¹`. Left Haar invariance and the published right
invariance supply the two measure-preserving maps. This proves all four
conjuncts of the target.

## Provenance and limits

The argument is an internal derivation from the project's published
`RankinSelberg.Measures`, `RankinSelberg.GeneralLinearUnimodularity`,
`Conductor.Congruence`, and `Group.GL.Maps`, together with pinned Mathlib's
`MeasureTheory/Measure/Haar/Unique.lean` and `MeasureTheory/Group/Measure.lean`.
It is not presented as a transcription of an external proof. The proof
preserves the original integral-subgroup normalization and all imported
constructions. It proves no character identity, transpose-invariance theorem
for distributions, character separation, or representation equivalence.
