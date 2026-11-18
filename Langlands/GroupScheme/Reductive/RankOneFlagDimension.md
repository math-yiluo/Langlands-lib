# The rank-one flag variety is a curve

Internal helper module of the Task 7586 proof of
`Langlands.GroupScheme.RankOneCentralCoverStatement`. It proves that the ordinary flag variety
`X = G/B` of `RankOneFlagSetup` has topological Krull dimension at most one, and that `U(ν)`
is not contained in `B`. The hypotheses are: `G` connected reductive over an algebraically
closed field, `i` a split maximal torus with pairwise dependent roots, and `B ⊇ T · U(-ν)` for
a suitable cocharacter `ν`.

## Cells in the flag variety

- `FlagData.mkCell ν hZ g hT hU` is the open cell (`RankOneFlagCell.Cell`) through a translate
  `g · x₀`, for the cocharacter `χ = ν ≫ i`. Its inputs are the facts that the centralizer of
  `χ` is represented by `i`, that `g · x₀` is torus-fixed, and that `g⁻¹ U(χ) g ⊆ B`. The three
  factors are the closed subgroups `Dynamic.Affine.unipotentScheme` of `U(-χ)` and `U(χ)`, and
  the torus. The open immersion of the triple cell is
  `Dynamic.isOpenImmersion_tripleCellMultiplication`.
- The instances `mkCell_isAffineHom`, `mkCell_locallyOfFiniteType` and `mkCell_quasiCompact`, and
  the theorem `mkCell_isUnipotent` (from `dynamicUnipotentUnipotence`), supply the hypotheses of
  the cell lemmas.
- `oppositeCocharacter_neg` and `oppositeCocharacter_pos`: the opposite of `-ν ≫ i` is `ν ≫ i`,
  and the opposite of `ν ≫ i` is `-ν ≫ i`.

## Core data

`CoreData i` extends flag data with a cocharacter `ν` and four facts:
- `hZp`, `hZn`: the centralizers of `ν ≫ i` and `-ν ≫ i` are the torus;
- `hconj`: conjugation by the Weyl point, `u ↦ n⁻¹ u n`, carries `U(ν)` into `U(-ν)`;
- `hB : U(-ν) ⊆ B`.

From these:
- `cell₀ = U(ν) · x₀` is the cell through `x₀` for `χ = -ν ≫ i`, and `cell₁ = U(-ν) · x₁` is the
  cell through `x₁` for `χ = ν ≫ i`. The point `x₁` is fixed by `U(ν)` because
  `n⁻¹ U(ν) n ⊆ U(-ν) ⊆ B`.
- `range_le_centralizer`: the image of every cocharacter of `T` centralizes `±ν`. It is used for
  the stability of the cells under torus cocharacters.
- `isFixed_neg`: a point fixed by `ν` is fixed by `-ν`.
- `x₁_isFixed_ν` and `x₀_isFixed_neg`: `x₁` is fixed by `ν`, and `x₀` by `-ν`. Both are
  restrictions of torus-fixedness.
- `eq_or_eq_of_isFixed_ν`: every rational point fixed by `ν` is `x₀` or `x₁`. This is the
  limit induction `SplitTorusLimitInduction.limit_induction` for the torus action, with
  `P` = fixed by `ν` and `R` = equal to `x₀` or `x₁`:
  - Limits preserve `ν`-fixedness (`isFixed_evalZero_of_isFixed`).
  - If a `ν`-fixed point has limit `x₀` (resp. `x₁`) along a cocharacter of `T`, it lies in
    `cell₀` (resp. `cell₁`) by `mem_opens_of_limit`, and `eq_of_isFixed` identifies it with the
    base point.
  - Torus-fixed points are `x₀` or `x₁` by `FlagData.eq_or_eq_of_isFixed`.
- `x₁_not_mem`: `x₁` is not in `cell₀`. Otherwise `eq_of_isFixed` would give `x₁ = x₀`.
- `eq_x₁_of_not_mem` (Bruhat decomposition of the rational points): a rational point outside
  `cell₀` is `x₁`. Its `ν`-limit exists by properness (`exists_isGmOrbitExtension`) and is
  `ν`-fixed, hence `x₀` or `x₁`. Limit `x₀` would put the point in `cell₀`. Limit `x₁` puts it in
  `cell₁`, where the two-limit lemma `eq_of_limit` gives the point `x₁`.
- `bot_eq_closedPoint` identifies the two names of the unique point of `Spec k`, and
  `exists_lift` lifts rational points of `X` to `G` (`exists_rationalPoint_lift_of_mem_range`).
- `not_mem_iff`: as a set, the complement of `cell₀` is the single point `x₁`. This uses the
  Jacobson subset lemma `ClosedRationalPoints.subset_singleton_of_rationalPoints`.
- `not_unipotent_le`: `U(ν)` is not contained in `B`. Otherwise every rational point of `cell₀`
  would be `x₀`, so `cell₀ = {x₀}` as a set. In the irreducible space `X`, the nonempty opens
  `cell₀` and `cell₁` meet, so `x₀ ∈ cell₁`, and `eq_of_isFixed` gives `x₀ = x₁`. This
  contradicts `x₀_ne_x₁`.
- `topologicalKrullDim_le_one`: `topologicalKrullDim X ≤ 1`. Suppose not:
  1. `KrullDimensionChain.exists_chain_of_not_le_one` gives a chain `y₀ ⤳ y₁ ⤳ c` of distinct
     points with `c` closed.
  2. `c` is a rational point `g · x₀`. Translation by `n g⁻¹` (`SchemeActionTranslation`) moves
     the chain to one ending at `x₁`.
  3. `X` is integral (`HomogeneousQuotient.smooth_reduced_irreducible_quotient`), with factorial
     local rings (`smoothAlgClosedFactorialStalks`). The Hartogs constancy lemma
     `HartogsAffineConstancy.exists_eq_const`, applied to the Chevalley map of `cell₀ = X \ {x₁}`,
     shows that this map is constant.
  4. By its injectivity on rational points, `cell₀` has the single rational point `x₀`, so
     `cell₀ = {x₀}` as a set.
  5. The two upper chain points lie in `cell₀`, so they coincide, a contradiction.

## Provenance

Internal: the classical argument that a homogeneous projective variety of a group of semisimple
rank one with two torus-fixed points is a curve, carried out with open cells, limits, Chevalley's
theorem and Hartogs' extension. It uses only the ordinary Borel quotient `G/B`. No quotient by a
dynamic parabolic, and no properness of one, is used. The by-products (`dim G/B ≤ 1`,
`U(ν) ⊄ B`) are internal lemmas of this proof.
