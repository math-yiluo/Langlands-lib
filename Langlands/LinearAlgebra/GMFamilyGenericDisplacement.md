# Points of `i(𝔞_M^G)^*` off the walls

Module `Langlands.LinearAlgebra.GMFamilyGenericDisplacement` describes the
points `λ = iΛ` at which all the denominators `θ_S` that occur in the proof of
Lapid's Lemma 8 are nonzero.

## Results

- `dualParam_apply`, `continuous_dualParam`, `dualParam_zero`: the map
  `x ↦ Λ_x = ⟪x, ·⟫` from `𝔞_M^G` to `StrongDual ℝ a` of
  `GMFamilyOrthogonalSetLimitStatement`.
- `root_mem_orthogonal_centralSpace`, `restrictedRoot_mem_orthogonal_centralSpace`:
  roots, and their restrictions to a Levi space containing `𝔞_G`, are
  orthogonal to `𝔞_G = centralSpace R`.
- `OffWalls R a Λ`: `Λ(α|_a) ≠ 0` for every root `α` whose restriction `α|_a`
  (`restrictedRoot a α`) is nonzero.
- `theta_ne_zero_of_offWalls`, `theta_ne_zero_of_offWalls_face`: off the
  walls, `θ_S(Λ) ≠ 0` for every chamber `S` of `a` for a root subset `R' ⊆ R`
  of which `a` is a Levi space, in particular for the Levi roots of a face
  `posSet R w` (`isLeviSpace_leviRoots` of `GMFamilyFaceRestriction`). The
  simple roots of `S` are nonzero restrictions of roots and their Gram volume
  is positive.
- `offWalls_dualParam_iff`: `Λ_x` is off the walls if and only if
  `⟪x, α⟫ ≠ 0` for every root with nonzero restriction to `a`.
- `ae_offWalls`: almost every `x ∈ 𝔞_M^G` (for the Euclidean volume) gives a
  point off the walls. The exceptional set is a finite union of kernels of the
  nonzero linear forms `x ↦ ⟪α, x⟫` on `𝔞_M^G` (nonzero because `α|_a`
  itself lies in `𝔞_M^G`), which are proper subspaces and hence null
  (`Measure.addHaar_submodule`).

## Provenance

The hyperplanes are those of Arthur's definition of `c_M` (J. Arthur, *An
introduction to the trace formula*, §17, (17.1) and Lemma 17.1, p. 94, in
`arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`, SHA-256
`88ba9a23fa62e2f62f14af7a5a2a8ffb062be29fc4590bf39c60c173add0a8a7`); the
statement that they are null sets is the remark on the integral in
`GMFamilyOrthogonalSetLimitStatement`. The proofs are derived directly.
