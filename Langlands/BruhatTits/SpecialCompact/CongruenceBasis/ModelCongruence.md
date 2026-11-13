# Model congruence subgroups as linear congruence subgroups

This internal unit identifies the congruence tower of an integral model with
pulled-back principal congruence subgroups. Here `F` is a nonarchimedean
local field with valuation ring `𝒪[F]`, `G` is a group scheme over `F`, and
`M : IntegralModel 𝒪[F] F G` is an integral model. The level-`n` congruence
subgroup `M.congruenceSubgroupAt n` is published
(`Langlands.GroupScheme.IntegralModel.CongruenceTower`). It is the image in
`rationalPoints G` of the integral sections whose reduction modulo `𝔪ⁿ`
(`M.reductionAt n`) is trivial.

The section `Matrices` fixes a square matrix `Mat` of elements of the
coordinate ring `M.coordAlg`. It assumes the comultiplication identity
`hcomul` and the counit identity `hcounit` of a matrix corepresentation.
These are the hypotheses of the published `modelRep`.

## Definitions

- `sectionMatrix M Mat x` is the matrix over `𝒪[F]` of values of the
  coordinates `Mat i j` at an integral section `x`. It is computed with the
  published `M.integralCoordinateAlgHom`.
- `conjugatedRep M Mat hcomul hcounit B` is the generic representation
  (`M.genericRep`) of the model representation
  `modelRep M.group M.coordIso Mat hcomul hcounit` followed by the inner
  automorphism of `GL_N` over `𝒪[F]` given by an integral matrix
  `B ∈ GL_N(𝒪[F])`.

## Results

- `modelRep_integralPointMap`: at the generic point of an integral section
  `x`, the matrix of the model representation is the image in `F` of
  `sectionMatrix M Mat x`. `sectionMatrix_one`: the identity section has the
  identity matrix. This follows from the previous identity, the
  multiplicativity of the generic representation and injectivity of
  `𝒪[F] → F`.
- `pointMatrix_conjugatedRep`: the `pointMatrix` of `conjugatedRep` at `g` is
  `B · (model matrix of g) · B⁻¹`, read in `GL_N(F)`. The proof uses the
  published `genericRep_rationalPointsEquiv` and `affineMatrix_comp_innerIso`.
- `isClosedSubgroup_conjugatedRep`: if the entries of `Mat` generate the
  coordinate algebra over `𝒪[F]`, then `conjugatedRep` is a closed subgroup
  embedding. The proof starts from the published `isClosedSubgroup_toGLHom`.
  It then composes with isomorphisms (`IsClosedSubgroup.of_iso`, `.comp`) and
  applies `IsClosedSubgroup.baseChange` along `Spec F → Spec 𝒪[F]`.
- `congruenceSubgroupAt_eq_linearCongruence`: **model congruence subgroups
  are linear.** Under the same generation hypothesis, for every `n : ℕ+`,
  `M.congruenceSubgroupAt n` equals
  `linearCongruence (conjugatedRep M Mat hcomul hcounit B) (algebraMap 𝒪[F] F) (𝔪ⁿ)`.
  The proof uses two published facts.
  - `M.reductionAt_eq_iff_of_adjoin_eq_top`: two integral sections have the
    same reduction modulo `𝔪ⁿ` exactly when the generators take congruent
    values. With `sectionMatrix_one`, an integral section has trivial
    reduction exactly when its coordinate matrix lies in
    `kernel 𝒪[F] (𝔪ⁿ)`.
  - `M.mem_integralPoints_iff_modelRep`: a rational point is integral exactly
    when its model matrix is the image of an element of `GL_N(𝒪[F])`.

  Since `kernel 𝒪[F] (𝔪ⁿ)` is normal, conjugation by `B` or `B⁻¹` moves
  between the two descriptions in both directions.
- `exists_model_linearCongruence`: **a diagonal linear model of the
  congruence tower.** Let `G` be connected reductive and let `χ` be a
  cocharacter `𝔾_m ⟶ M.group` of the integral model. Then there exist `N`, a
  representation `ρ` of `G` on `F^N` and weights `e` with the following three
  properties: `ρ` is a closed subgroup embedding;
  `M.genericCocharacter χ ≫ ρ` is the diagonal cocharacter with weights `e`;
  and `M.congruenceSubgroupAt n = linearCongruence ρ (algebraMap 𝒪[F] F) (𝔪ⁿ)`
  for every `n`. The published `M.exists_integral_matrixCoefficients`
  supplies `Mat` together with its corepresentation identities and
  generation. The published
  `exists_innerIso_comp_eq_diagonalCocharacter_of_isPrincipalIdealRing`
  (over the principal ideal ring `𝒪[F]`) supplies `B` and `e` diagonalizing
  `χ ≫ modelRep`. Then `ρ := conjugatedRep M Mat hcomul hcounit B`. The
  diagonal identity follows from `genericCocharacter_comp_genericRep` and
  `baseChangeCocharacter_diagonalCocharacter`.

The provenance is internal composition of the published integral-model
results named above. No literature statement is formalized here.
