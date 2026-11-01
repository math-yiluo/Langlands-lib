# Groups for the cyclic orbit of the right `Φ⁻` sequence

Author: Worker 837.

This helper module belongs to the proof of the clause
`Langlands.Derivative.MirabolicProductMinus.RightPhiShortExact.{uF,uV} F T` of
`Langlands.Representation.Derivative.MirabolicProductMinusCompatibilityStatement`
(host task `6cd54f76-f453-4faa-818a-5843e1bbcaff`). It supplies the group data of
the published split-stage character comparison at the cyclic representative,
the restriction of the positive character to the kernel intersection, and the
Haar ratio of that comparison. The cyclic piece is assembled in
`Langlands.Representation.Derivative.MirabolicProductMinusRightPhiCycle`.

## Provenance

All declarations are derived internal content: elementary matrix-group facts,
one character restriction and one Haar-measure computation. BZ77 §7.2, printed
p.471 (PDF p.32), source `bernstein-zelevinsky-1977-induced-i`, treats the two
orbits of the right mixed subgroup on `P_(n-1) V_n` with the geometric lemma and
leaves the details to the reader; the cyclic orbit is the open one and gives the
subobject `Φ⁻(τ) × ρ` of 4.13(c). Here it is computed through the published
`Induction.SplitStagesCharacter.comparisonEquiv`, with group data
`G = Q = P_(t+1) V_(t+2)` (`plusSubgroup t`, `t = k+r+1`), `L = P_(t+1)`,
`r = plusProjection`, `s = plusSuccessor`, the stages subgroup
`P = rightStages k r R 0` and the stabilizer `S`. The generic stages lemmas
(`plusKernel_le_stagesSubgroup`, `mem_stagesSubgroup_comap_iff`,
`plusSuccessor_mem_orbitStabilizer`, `plusKernelThetaSmooth`,
`determinantNorm_rankCast_symm`, `plusKernelContinuousEquiv`) are those of
`MirabolicProductMinusRightPhiIdentityGroups`.

## Determinants of the right mixed subgroup

- `det_rightSubgroup`: for `g ∈ rightSubgroup k n` the determinant is the product
  of the determinants of the diagonal blocks `(rightProjection g).1` and
  `(rightProjection g).2` (published `rightMatrix_parts`, block-triangular
  determinant).
- `determinantNorm_rightSubgroup`: hence `ν_(k+n+1)(g) = ν_(n+1)(p) ν_k(a)` for the
  normalized determinant norm `T.determinantNorm`.

## The cyclic orbit

Fix `k, r` and a commutative ring `R`; `H = rightInducing k r`,
`w = rightRepresentative k r R 0` (the published cycle).

- `rightCycStabilizer k r R` is the stabilizer `Q ∩ w H w⁻¹` with the ambient
  group written `mirabolic (k+r+1+1)`, the form of the orbit pieces of the
  plus-subgroup Mackey filtration. It is the published `rightStabilizer k r R 0`
  up to the presentation `k+r+2 = k+r+1+1`; `rightCycStabilizer_le_stages` and
  `rightCycStabilizer_isClosed` are the published `rightStabilizer_le_stages`
  and `rightStabilizer_isClosed`.
- `mem_rightStages_zero_comap_iff`: `K = P.comap plusSuccessor` consists of the
  `l` with `rankCast⁻¹ l ∈ rightSubgroup (k+1) r` (published
  `mem_rightSection_zero_iff`), i.e. `l = [[p, X], [0, a]]` with `p ∈ P_(r+1)`
  and `a ∈ GL_(k+1)` after the rank cast `(k+1)+r = k+r+1`.
  `rightCycleToSection` and its `_val` view `l` in the published
  `rightSection k r R 0`; `rightCycleLevi l = ⟨rankCast⁻¹ l, _⟩`, with
  `rightCycleLevi_val` and `rightCycleLevi_eq` relating it to the published
  `rightCycleSectionEquiv`.
- `rightCycle_section_mem`: `plusSuccessor l ∈ S` for `l ∈ K`;
  `rightCycleSectionElement l` is that element of `S`.
- `rightCycleInclusion : S →* rightSubgroup (k+1) (r+1)` is the published
  `stabilizerToInducing` followed by `rightInducingHom`;
  `rightCycleInclusion_val` gives `rankCast⁻¹ (w⁻¹ q w)`.
  `rightCoefficient_zero_apply`: the published `rightCoefficient k r R 0` is
  `rightProjection` of it.
- `rightCoefficient_rightCycleSectionElement`: on `plusSuccessor l` the blocks are
  `(successor p, a)` with `(p, a) = rightProjection (rightCycleLevi l)`, from the
  published `rightSectionCoefficient_zero`.
- `rightCycleKernelEquiv : S ∩ ker plusProjection ≃* rightPsiKernel (k+1) (r+1)`
  (the published kernel subgroup of the right mixed subgroup), by
  `rightCycleInclusion`, with inverse `g ↦ w (rankCast g) w⁻¹`;
  `rightCycleKernelEquiv_val` and the homeomorphic version
  `rightCycleKernelContinuousEquiv`.
- `thetaPlus_rightCycle`: for `n ∈ S ∩ ker plusProjection`,
  `thetaPlus ψ (k+r+1) n = θ_r(rightPsiKernelEquiv (rightCycleKernelEquiv n))`,
  where `θ_r = Mirabolic.theta ψ r` is the character of the radical `V_(r+2)` of
  `P_(r+2)`. This is the published `rightOrbitTheta_zero`
  (`MirabolicMixedOrbitCharacters`: the ambient positive character on the cyclic
  radical intersection is `θ_r` through the actual coefficient), applied to the
  same matrix viewed in `rightRadicalIntersection k r R 0`. It is the only use of
  that module.

## Split-stage data and the Haar ratio

- `rightCycleRetraction k r R` is the published `splitStagesRetraction`
  `P → K` for `plusProjection`, `plusSuccessor`, `P = rightStages k r R 0`;
  `rightCycleInducing k r R = S.subgroupOf P`; `rightCycleInducing_section_mem`
  is the section containment.
- `determinantNorm_rightCycle`: `ν(l) = ν(p) ν(a)` for `l ∈ K`
  (`determinantNorm_rightSubgroup` at `rightCycleLevi l`).
- `rightCycleHaarRatio_apply`: the published `splitKernelHaarRatio` of the
  comparison is `ν(a) = |det a|` at `l`. Inverse conjugation by `plusSuccessor l`
  scales Haar measure on the kernel `≅ V_(k+r+3)` by `ν(l)⁻¹` (published
  `mulEquivHaarChar_conj_levi_inv`, transported along
  `splitStagesKernelContinuousEquiv` and `plusKernelContinuousEquiv` with
  `haarChar_eq_of_conjugacy`). On the intersection, transported to `V_(r+2)` by
  `splitStagesCoefficientIntersectionContinuousEquiv`,
  `rightCycleKernelContinuousEquiv` and `rightPsiKernelContinuousEquiv`, it is
  conjugation by `(levi p)⁻¹`, `p` viewed in `GL_(r+1)` (the first block of the
  coefficient of `plusSuccessor l` is `successor p = levi p`), with character
  `ν(p)⁻¹`. The ratio
  is `ν(p)⁻¹ / ν(l)⁻¹ = ν(a)`.

## Imports

The direct imports are `MirabolicProductMinusRightPhiIdentityGroups` (generic
stages data, `plusKernelThetaSmooth`, rank-cast facts, and through it the
published orbit, stages, section-coefficient, Mackey and right-`Ψ⁻` group
modules) and the published `MirabolicMixedOrbitCharacters` (only
`rightOrbitTheta_zero`). The complete import closure and the restriction audit
are recorded in `Langlands/Representation/Derivative/MirabolicProductMinusRightPhi.md`.
