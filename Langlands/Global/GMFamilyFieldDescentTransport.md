# Transport of the field-descent formula along an isometric embedding

This module transports the field-descent formula from a root set `R₀` in a Euclidean space `E₀`
to the restricted roots `restrictRoots φ R₀` on a subspace given by an isometric embedding
`φ : E →ₗᵢ[ℝ] E₀` ([GMFamilyRootRestriction](../LinearAlgebra/GMFamilyRootRestriction.md)). In Arthur's setting
(J. Arthur, *An introduction to the trace formula* (2005), Lemma 17.5,
`arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura`) `E₀` carries the roots of a maximal
split torus over the larger field and `E = 𝔞_{M₁}`.

## Contents

- Auxiliary transport lemmas: `up_mono`, `isFamily_congr` and `cM_congr` (families and `cM` along
  an equality of root sets), `mapSub_coarseCenter`, `coarseCenter_le_of_mem_leviSpaces`,
  `le_of_mem_leviSpaces'`, the continuous linear map `pushParamL` with `contDiff_pushParam`,
  and `fine_eq_inducedFamily_up`, `inducedFamily_eq_up`, `pushFam_inducedFamily` (induced families
  commute with `pushFam`).
- `hasFieldDescentFormulaIn_of_mapSub`: if `HasFieldDescentFormulaIn` holds for `R₀` (closed under
  negation), `φ(V)` and `φ(b)`, it holds for the restricted roots, `V` and `b ≤ V`. A family `c₁`
  on `V` is pushed to `φ(V)` (`isFamily_pushFam_iff`); the induced families, the functions `cM`
  and `cQM`, the faces, the Levi flats, the descent coefficients and the descent sections
  correspond under `φ` by the lemmas of
  [GMFamilyRootRestriction](../LinearAlgebra/GMFamilyRootRestriction.md). The smooth functions
  `c₀` and `cQ` are pulled back by composing with the smooth maps `pushParam`.
- `starProjection_mapSub`, `centralSpace_eq_mapSub` and `isCentreSplit_mapSub`: when the central
  space of `R₀` lies in `φ(E)`, it is the image of the central space of the restricted roots, and
  compatibility of `b` with the central projection transfers to `φ(b)`.
- `isSpecialSubspace_mapSub`: if the sums over each nonzero restriction `β` to `b` of the
  restricted roots `α`, weighted by the total weight `Σ_{res γ = α} m₀ γ` of the roots restricting
  to `α`, lie in `b`, then `φ(b)` is special in `φ(E)` for the weights `m₀`
  (`coe_restrictedRoot_top` is used for the whole space).
- `hasFieldDescentFormula_of_restrictRoots`: for a root set `R₀`, with `φ(E)` a Levi flat of `R₀`,
  `b` compatible with the central projection and the weighted sums as above for positive weights,
  `HasFieldDescentFormula (restrictRoots φ R₀) b` holds. It combines `hasFieldDescentFormulaIn`
  ([GMFamilyFieldDescentRoots](GMFamilyFieldDescentRoots.md)) for `R₀`, `φ(E)` and `φ(b)` with the
  transport above.
