# Groups for the positive-rank right `Ψ⁻` compatibility of BZ77 4.13(c)

Author: Worker 837.

This helper module belongs to the proof of the clause
`Langlands.Derivative.MirabolicProductMinus.RightPsiCompatibility.{uF,uV} F T`
of the published statement module
`Langlands.Representation.Derivative.MirabolicProductMinusCompatibilityStatement`.
It supplies the subgroups, block coordinates, kernel identification and Haar
ratio used at positive ranks. The final clause is assembled in
`Langlands.Representation.Derivative.MirabolicProductMinusRightPsi`.

## Provenance

All declarations are derived internal content for that proof. They are
elementary matrix-group facts and one Haar-measure computation. BZ77 §7.2
(printed p.471, source `bernstein-zelevinsky-1977-induced-i`) proves the
`Ψ⁻` part of 4.13(c) with the geometric lemma, using a single orbit. This
module instead prepares the published two-stage compact-induction comparison
`Induction.splitStagesCompactEquiv`.

Two shared lower modules provide the elementary lemmas:

- `Langlands.GeneralLinear.determinant_blockParabolic` in
  `Langlands.Group.GL.BlockDeterminant` is the unchanged proof formerly
  private in `TwistedProductCharacterTwistProof`.
- `Langlands.Geometric.haarChar_eq_of_conjugacy` in
  `Langlands.HarmonicAnalysis.HaarConjugacy` is the unchanged public theorem
  moved from `ParabolicOrbitHaarTransport`.

The integration removes the local copies and imports these modules directly.
Their dependencies contain no classification or orbit consumers.

## Setting

Throughout, `m, r : ℕ` with `0 < r` and `0 < m`, and `R` is a commutative
ring (the p-adic field in the Haar section). The mirabolic group
`mirabolic (m + r) R` is `P_(m+r+1)`. The published case (III) subgroup is
`H = rightSubgroup m r R`. The published `rightProjection` sends `H` to
`mirabolic r R × GL_m R`, and `rightSection` is its section. These
declarations come from `Langlands.Group.GL.MirabolicMixedProductSubgroups`.

## Indices and the parabolic `Q`

- `rightPsiFirst j` (`j : Fin r`) and `rightPsiSecond i` (`i : Fin m`) are
  the first `r` and the last `m` coordinates of `Fin (m + r)`. The lemmas give
  their values, injectivity and disjointness, their relation to the published
  `rightIndex`, and the fact that every coordinate is one of them
  (`rightPsi_cases`).
- `rightPsiCast m r R : GL_(m+r) ≃* GL_(r+m)` is entry-preserving reindexing
  along `Fin.cast`. `rightPsiCast_eq` shows it equals
  `generalLinearCastHom (Nat.add_comm r m)`, from the helper
  `MirabolicProductMinusRightPsiZero`.
- `rightPsiParabolic hr hm = Q` is the preimage under `rightPsiCast` of the
  published binary parabolic `(BlockShape.binary r m hr hm).parabolic R`.
  `mem_rightPsiParabolic_iff` says that `g ∈ Q` exactly when the last `m`
  rows of `g` vanish on the first `r` columns, i.e. `g = [[A, X], [0, D]]`.
- `rightPsiStages hr hm = P` is the preimage of `Q` under the published
  `projection : P_(m+r+1) → GL_(m+r)`. The lemmas show:
  - `ker projection ≤ P` (`ker_projection_le_rightPsiStages`);
  - `H ≤ P` (`rightSubgroup_le_rightPsiStages`);
  - `levi l ∈ H` for `l ∈ Q` (`levi_mem_rightSubgroup`);
  - `levi l ∈ P ↔ l ∈ Q` (`levi_mem_rightPsiStages_iff`);
  - the section of `P` over `K = P.comap levi` takes values in `H`
    (`rightPsiStages_section_mem`).
- `continuous_rightPsiCast`, `isClosed_rightPsiParabolic` and
  `isClosed_rightPsiStages` give continuity and closedness.

## The diagonal blocks

- `determinant_blockParabolic B g`: the determinant of an element of a
  standard block parabolic is the product of the determinants of its diagonal
  blocks. The proof uses Mathlib's block-triangular determinant formula.
- `rightPsiFirstBlock hr hm l hl = A ∈ GL_r` and
  `rightPsiSecondBlock hr hm l hl = D ∈ GL_m` are the two published
  `leviProjection` blocks of `rightPsiCast l`. Their `_apply` lemmas give
  their entries as `l (first i) (first j)` and `l (second i) (second j)`.
- `determinant_rightPsi`: `det l = det A · det D` on `Q`.
- `rightProjection_levi`: for `l ∈ Q` the case (III) blocks of `diag(l, 1)`
  are `(diag(A, 1), D)`.

## The kernel `N`

- `rightPsiKernel m r R = N` is the subgroup of `H` lying in
  `ker projection`.
- `rightPsiKernelEquiv : N ≃* radical r R` sends `g` to the mirabolic block
  `(rightProjection g).1`, which lies in the radical `V_(r+1)` of `P_(r+1)`.
  Its inverse is `u ↦ rightSection (u, 1)`. The supporting lemmas are
  `projection_entry_of_eq_one`, `rightProjection_fst_mem_radical`,
  `rightProjection_snd_of_mem_kernel`, `projection_rightSection_radical` and
  `rightSection_of_mem_kernel`.
- `rightProjection_of_mem_kernel`: on `N` the case (III) blocks are `(u, 1)`.
- `rightPsiKernelContinuousEquiv` is the same map as an isomorphism of
  topological groups.

## Split-stage data

- `rightPsiRetraction hr hm : P →* K` is the published
  `Induction.splitStagesRetraction` for `projection`, `levi`, `P`.
- `rightPsiInducing hr hm = H.subgroupOf P` is the inducing subgroup inside
  `P`. `isClosed_rightPsiInducing` states that it is closed.
  `rightPsiSection_mem` states that the section lies in it.
- `rightPsiLevi_mem`: an element of `K` lies in `Q`.

## The Haar ratio

- `Langlands.Geometric.haarChar_eq_of_conjugacy e a b h`: conjugate topological automorphisms
  have equal Haar scaling characters.
- `mulEquivHaarChar_splitKernelConjugation_levi T n l`: conjugation by
  `diag(l, 1)⁻¹` on `ker projection` of `P_(n+1)` scales Haar measure by
  `|det l|⁻¹`. This comes from the published `mulEquivHaarChar_conj_levi_inv`,
  transported along `ker projection = radical`.
- `determinantNorm_rightPsi`: `|det l| = |det A| · |det D|` on `Q`.
- `rightPsiHaarRatio_apply T hr hm l`: the published `splitKernelHaarRatio`
  of the comparison is `|det D|` at `l = [[A, X], [0, D]] ∈ K`. That ratio is
  the Haar character of conjugation on the intersection
  `I = HP ∩ ker(rP)` divided by the Haar character of conjugation on
  `ker(rP)`. The published `splitStagesKernelContinuousEquiv` identifies
  `ker(rP)` with `ker projection = V_(m+r+1)`, where the character is
  `|det l|⁻¹`. The published
  `splitStagesCoefficientIntersectionContinuousEquiv`, followed by
  `rightPsiKernelContinuousEquiv`, identifies `I` with `N ≅ V_(r+1)`. There
  conjugation becomes conjugation by `diag(A, 1)⁻¹` (`rightProjection_levi`),
  so its character is `|det A|⁻¹`. The ratio is
  `|det A|⁻¹ / (|det A| |det D|)⁻¹ = |det D|`.

## Imports

The direct imports include `Langlands.Group.GL.BlockDeterminant`,
`Langlands.HarmonicAnalysis.HaarConjugacy`, the helper
`Langlands.Representation.Derivative.MirabolicProductMinusRightPsiZero` and
the published `Langlands.Representation.Induction.BinaryPositiveCompact`,
which brings the split-stage modules, the binary product and the block
modulus. The complete import closure of the clause and its restriction audit
are recorded in
`Langlands/Representation/Derivative/MirabolicProductMinusRightPsi.md`.
