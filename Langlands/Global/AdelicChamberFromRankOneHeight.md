# Minimal-parabolic norm-one factors and chamber reduction from the rank-one bound

Author: Worker 5269.

This internal derived auxiliary unit does two things:

1. It proves, for every actual algebraic Siegel setup, that each ambient norm-one point
   of the minimal parabolic can be written as a product of parabolic factors.
2. It uses these factors to reduce `AdelicSiegelChamberReductionStatement` to the
   universal rank-one arithmetic statement `RankOneParabolicRationalOrbitHeightBoundStatement`
   alone.

The rank-one statement is an explicit hypothesis of the reduction. This unit does not
prove it, so the chamber statement itself remains unproved.

## The definition

Fix a number field `F`, an affine group scheme `G` over `F`, a torus `T` with
`i : T → G`, a cocharacter `ν`, and `j : T₀ → T`. Write `P`, `N` and `M` for the
canonical schemes `Standard.parabolicScheme i ν ∅`, `Standard.unipotentScheme i ν ∅`
and `Standard.leviScheme i ν ∅`, with the canonical maps `ι_N`, `ι_M` into `G`.

`HasMinimalParabolicNormFactors F G T i ν T₀ j` states the following. Let `p` be in
`normOneSubgroup F G` (the ambient `G(𝔸_F)¹`, defined by the characters of **G**) and
in the actual image `standardParabolicImage F G T i ν` of `P(𝔸_F)`. Then there exist

- `n ∈ N(𝔸_F)`,
- `m ∈ normOneSubgroup F M` (the intrinsic `M(𝔸_F)¹`, defined by the characters of `M`),
- `a ∈ PositiveRealTorus.intrinsicSubgroup F T₀` (an intrinsic positive point of `T₀`),

such that `ι_N(n) * ι_M(m) * positiveMap F G T i T₀ j a = p`.

Only existence is asserted. There is no uniqueness, continuity or topological
statement, and there is no compact subgroup. The property is therefore strictly weaker
than the published `HasMinimalParabolicNormCoordinates`, which asks for a homeomorphism
`N(𝔸_F) × (M(𝔸_F)¹ × A_{T₀}) ≃ₜ P(𝔸_F) ∩ G(𝔸_F)¹` with the same ambient value. The
published chamber assembly uses only this surjectivity.

### Provenance

This is a **derived** structural property, not a verbatim statement of the source.
Springer, *Reduction theory over global fields* (1994), §2.1, printed p.211
(PDF p.5), writes `P` as the semidirect product of the Levi group `L` and the unipotent
radical `U`. It then observes that `P(𝔸) = F·S(𝔸)·P(𝔸)¹` for a finite subset `F` of
`P(𝔸)`. In the fundamental set (F) on printed p.212, the parabolic part of a
Siegel set is `S(c)·P(𝔸)¹` with `S(c) ⊂ S(𝔸) ∩ G(𝔸)¹`.
`HasMinimalParabolicNormFactors` records the corresponding factorization of
`P(𝔸) ∩ G(𝔸)¹` in the Library's terms. Springer's `U` corresponds to `N`, and `L` to `M`.
The positive part is taken from the intrinsic positive real points of the derived split
torus `T₀`, as in `AdelicSiegelChamberReductionStatement`. The comparison is proved below
from the Library's setup, not assumed.

## The factor theorem

`IsSiegelAlgebraicSetup.hasMinimalParabolicNormFactors` proves the property for
connected reductive `G` and every actual `IsSiegelAlgebraicSetup F G T i ν T₀ j`. Its
proof has five steps.

1. **Unipotent factor.** `exists_standardLeviPart` gives a homomorphism `f` on
   `standardParabolicImage`. Its values lie in `standardLeviImage`, it is the identity
   there, and its kernel is `standardUnipotentImage`. Hence `p (f p)⁻¹` lies in the
   kernel, which gives `n` with `ι_N(n) = p (f p)⁻¹`, and `f p = ι_M(m_M)` for some
   `m_M ∈ M(𝔸_F)`.
2. **Positive decomposition of `M`.** The torus factor `torusToStandardLevi : T → M` is
   maximal split, because the setup's `T` is maximal split in `G`
   (`isMaximalSplitTorus_standardLeviTorusFactor`). It is also central in `M`, because
   `M` is the centralizer of `T` (setup field `hlevi`). So it is a split component of the
   connected reductive `M`. `PositiveRealTorus.splitComponentNormOneDecomposition` for `M`
   (with `centralSplitTorusCharacter`) is a group isomorphism, and its surjectivity
   writes `m_M` as a positive point `a_T` of `T` times `n_M ∈ M(𝔸_F)¹`.
3. **Lifting to `T₀ × Z₀`.** The setup supplies a split component `Z₀ → G` (through
   `z : Z₀ → T`) and a surjective product morphism `T₀ × Z₀ → T`.
   `hasPositiveProductFactorization_of_surjective_product` writes `a_T` as the product
   of the images of `a₀ ∈ A_{T₀}` and `z₀ ∈ A_{Z₀}`.
4. **Collecting factors.** Centrality of `T` in `M` and functoriality of adelic points give
   `p = ι_N(n) · ι_M(n_M) · positiveMap(a₀) · Z`, where `Z` is the image of `z₀` in
   `G(𝔸_F)`. The unipotent factor is norm one because characters are trivial along `N`
   (`charactersTrivialAlong_unipotent`). The Levi factor is norm one because adelic
   point maps preserve norm-one subgroups (`map_normOneSubgroup_le`). The positive
   factor is norm one by `positiveMap_mem_normOne`. Hence `Z` is norm one.
5. **The `Z₀` factor vanishes.** `PositiveRealTorus.splitComponentNormOneDecomposition`
   for `G` along `Z₀` is injective. It sends `(z₀, 1)` and `(1, Z)` to the same point,
   so `Z = 1`.

So `(n, n_M, a₀)` are the required factors.

The helper `adelicPointsMap_comp_apply` records that the adelic-point map of a
composite is the composite of the adelic-point maps.

`HasMinimalParabolicNormFactors.exists_iwasawa_factors` combines the factors with a
prescribed parabolic Iwasawa compact subgroup `K` (`IsParabolicIwasawaCompact` for `P`).
For `g ∈ G(𝔸_F)¹` write `g = p k` with `p ∈ P(𝔸_F)` and `k ∈ K`. Then
`k ∈ G(𝔸_F)¹` (`compactSubgroup_le_normOneSubgroup`), so `p ∈ P(𝔸_F) ∩ G(𝔸_F)¹`.
Factoring `p` gives `ι_N(n) ι_M(m) positiveMap(a) k = g`. This matches the published
`HasMinimalParabolicNormCoordinates.exists_iwasawa_factors`, but it needs only the
factor property.

## The chamber reduction

`hasWeakChamberReduction_of_rankOne_height` proves `HasWeakChamberReduction` for a fixed
connected reductive `G` of locally finite type, a fixed actual setup, and its prescribed
Iwasawa compact `K`. It assumes `RankOneParabolicRationalOrbitHeightBoundStatement`.
The proof copies the published
`hasWeakChamberReduction_of_rootLevi_height_and_coordinates`
(`AdelicChamberFromRootLeviBounds`) step by step. The only change is the Iwasawa
factorization, which comes from
`HasMinimalParabolicNormFactors.exists_iwasawa_factors` and the factor theorem above
instead of from the coordinate premise. The argument runs as follows.

- Enumerate the finite simple relative roots. At each index take the maximal standard
  parabolic obtained by deleting that root, with exact Chevalley eigenlines and
  simultaneous rational right minima (`exists_adapted_standardParabolicPrefix_minima`).
- Transfer the minimum inequalities through a left compact factor
  (`exists_pos_chainHeightMinimalSet_compact_transport`).
- Apply the published root bound
  `hasUniformRootBound_of_minimal_coordinates_and_prefix_minima`, with the rank-one
  hypothesis, to the family of torus points occurring in such minimal products. By
  finiteness this gives one lower chamber constant `t`.
- For `g ∈ G(𝔸_F)¹`, choose a rational `q` minimizing `g⁻¹` on the right, and factor
  `q⁻¹ g = ι_N(x) ι_M(m) positiveMap(a) k`.
- Invert this product and commute the torus and minimal-Levi images
  (`commute_torus_minimalLevi`). This places the inverse torus point in the bounded
  family, so `a` lies in the weak simple-root chamber of parameter `t`. The rational
  point `q⁻¹` acts on the left and `k ∈ K`.

`adelicSiegelChamberReduction_of_rankOne_height` packages this as the implication

`RankOneParabolicRationalOrbitHeightBoundStatement.{u} → AdelicSiegelChamberReductionStatement.{u}`

in an arbitrary universe. Compared with the published
`adelicSiegelChamberReduction_of_rankOne_height_and_coordinates`, the premise
`MinimalParabolicNormCoordinatesStatement` is removed. This is conditional progress,
not a proof of the chamber statement. No external result is assumed beyond the
explicit rank-one hypothesis and the imported Library theorems named above.
