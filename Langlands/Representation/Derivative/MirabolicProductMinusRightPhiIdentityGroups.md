# Groups for the identity orbit of the right `Φ⁻` sequence

Author: Worker 837.

This helper module belongs to the proof of the clause
`Langlands.Derivative.MirabolicProductMinus.RightPhiShortExact.{uF,uV} F T` of
`Langlands.Representation.Derivative.MirabolicProductMinusCompatibilityStatement`
(host task `6cd54f76-f453-4faa-818a-5843e1bbcaff`). It supplies the group data of
the published split-stage character comparison at the identity representative,
and the Haar ratio of that comparison. The identity piece is assembled in
`Langlands.Representation.Derivative.MirabolicProductMinusRightPhiIdentity`.

## Provenance

All declarations are derived internal content: elementary matrix-group facts
and one Haar-measure computation. BZ77 §7.2, printed p.471 (PDF p.32), source
`bernstein-zelevinsky-1977-induced-i`, treats the two orbits of the right mixed
subgroup on `P_(n-1) V_n` with the geometric lemma and leaves the details to the
reader. Here the identity orbit is computed through the published
`Induction.SplitStagesCharacter.comparisonEquiv`, whose group data are
`G = Q = P_(t+1) V_(t+2)` (`plusSubgroup t`, `t = k+r+1`), `L = P_(t+1)`,
`r = plusProjection`, `s = plusSuccessor`, the stages subgroup `P` and the
stabilizer `S`.

## Stages data at an arbitrary representative

For `H ≤ P_(t+2)` and `w ∈ P_(t+2)`, with the published
`stagesSubgroup H w` and `sectionSubgroup H w` (`MirabolicMixedOrbitData`):

- `plusKernel_le_stagesSubgroup`: the kernel of `plusProjection` lies in the
  stages subgroup;
- `mem_stagesSubgroup_comap_iff`: the preimage of the stages subgroup under
  `plusSuccessor` is the section subgroup (`plusProjection ∘ plusSuccessor = id`);
- `plusSuccessor_mem_orbitStabilizer`: successors of that preimage lie in the
  stabilizer `orbitStabilizer H Q w`.

## The kernel character

- `plusKernelThetaSmooth T ψ t`: the published `plusKernelTheta ψ t`
  (`thetaPlus` restricted to `ker plusProjection`) as a smooth character; its
  kernel is open because it is `θ_ψ` through `plusKernelEquiv`
  (`mirabolicTheta_isOpen_ker`).
- `plusKernelThetaSmooth_sectionInvariant`: it is fixed by inverse conjugation by
  successors, since `thetaPlus` is a character of `Q` trivial on successors
  (`thetaPlus_plusSuccessor`).

`rankCast_rfl_apply`, `rankCast_rfl_symm_apply`,
`projection_rankCast_eq_one_iff` and `projection_rankCast_symm_eq_one_iff` are
elementary facts about the published entrywise `rankCast`.

## The identity orbit

Fix `k, r` and a commutative ring `R`; `H = rightInducing k r`, `w = 1`.

- `rightIdStabilizer k r R` is the stabilizer `Q ∩ H` with the ambient group
  written `mirabolic (k+r+1+1)`, the form of the orbit pieces of the
  plus-subgroup Mackey filtration. It is the published
  `rightStabilizer k r R 1` up to the presentation `k+r+2 = k+r+1+1`;
  `rightIdStabilizer_le_stages` and `rightIdStabilizer_isClosed` are the
  published `rightStabilizer_le_stages` and `rightStabilizer_isClosed`.
- `mem_rightStages_one_comap_iff`: `K = P.comap plusSuccessor` consists of the
  `l` with `rankCast⁻¹ l ∈ leftSubgroup (r+1) k` (published
  `mem_rightSection_one_iff`). `rightIdentityToSection` and its `_val` view an
  element of `K` in the published `rightSection k r R 1`;
  `rightIdentityLevi l = ⟨rankCast⁻¹ l, _⟩ ∈ leftSubgroup (r+1) k`, the lower
  left mixed coordinates `[[A, B], [0, D]]`, with `rightIdentityLevi_eq`
  relating it to the published `rightIdentitySectionEquiv`.
- `rightIdentity_section_mem`: `plusSuccessor l ∈ S` for `l ∈ K`;
  `rightIdentitySectionElement l` is that element of `S`.
- `rightStabilizer_one_lastColumn`: for `q ∈ S`, the entry of `q` in row
  `k+r+1` and the last column vanishes. Through `rankCast` this row lies in the
  `GL_(k+1)` block of `rightSubgroup (k+1) (r+1)`, whose entries outside the
  diagonal block vanish there (`mem_rightSubgroup_iff_entry`).
  `thetaPlus_rightStabilizer_one`: hence `thetaPlus ψ (k+r+1) q = ψ(0) = 1`.
- `rightIdentityInclusion : S →* rightSubgroup (k+1) (r+1)` is the published
  `stabilizerToInducing` followed by `rightInducingHom`; `rightIdentityInclusion_val`
  gives `rankCast⁻¹ q`. `rightCoefficient_one_apply`: the published
  `rightCoefficient k r R 1` is `rightProjection` of it.
- `rightCoefficient_rightIdentitySectionElement`: on `plusSuccessor l` the
  blocks are `(levi A, D)` with `(A, D) = leftProjection (rightIdentityLevi l)`,
  from the published `rightSectionCoefficient_one`.
- `rightIdentityKernelEquiv : S ∩ ker plusProjection ≃* rightPsiKernel (k+1) (r+1)`
  (the published kernel subgroup of the right mixed subgroup), by
  `rightIdentityInclusion` with inverse `rankCast`; `rightIdentityKernelContinuousEquiv`
  is its homeomorphic version.

## Split-stage data and the Haar ratio

- `rightIdentityRetraction k r R` is the published `splitStagesRetraction`
  `P → K` for `plusProjection`, `plusSuccessor`, `P = rightStages k r R 1`;
  `rightIdentityInducing k r R = S.subgroupOf P`;
  `rightIdentityInducing_section_mem` is the section containment.
- `determinantNorm_rankCast_symm`: `rankCast` keeps the normalized
  determinant norm. `plusKernelContinuousEquiv` is the published
  `plusKernelEquiv` as a topological isomorphism.
- `determinantNorm_rightIdentity`: `ν(l) = ν(A) ν(D)` for `l ∈ K`, from the
  published `determinantNorm_leftSubgroup`.
- `rightIdentityHaarRatio_apply`: the published `splitKernelHaarRatio` of the
  comparison is `ν(D) = |det D|` at `l`. Inverse conjugation by `plusSuccessor l`
  scales Haar measure on the kernel `≅ V_(k+r+3)` by `ν(l)⁻¹` (published
  `mulEquivHaarChar_conj_levi_inv`, transported along
  `splitStagesKernelContinuousEquiv` and `plusKernelContinuousEquiv` with
  `haarChar_eq_of_conjugacy`). On the intersection, transported to
  `V_(r+2)` by `splitStagesCoefficientIntersectionContinuousEquiv`,
  `rightIdentityKernelContinuousEquiv` and `rightPsiKernelContinuousEquiv`, it is
  conjugation by `(levi A)⁻¹`, with character `ν(A)⁻¹`. The ratio is
  `ν(A)⁻¹ / ν(l)⁻¹ = ν(D)`.

## Imports

The direct imports are the published `MirabolicMixedOrbitSectionCoefficients`,
`MirabolicMixedOrbitStages`, `MirabolicPhiMinusMackey`,
`MirabolicProductMinusRightPsiGroups` (for `rightPsiKernel` and its
equivalences), `LeftMixedProductSuccessor` (for `determinantNorm_leftSubgroup`)
and `SplitStagesCharacterComparison`. The complete import closure and the
restriction audit are recorded in
`Langlands/Representation/Derivative/MirabolicProductMinusRightPhiIdentity.md`.
