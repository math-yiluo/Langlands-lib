# Springer's split fundamental set from the split rank-one height bound

Author: Worker 5253.

This internal derived module proves Springer's split fundamental-set statement
`SplitAdelicFundamentalSetStatement` (`AdelicSplitFundamentalSet`) from two explicit
hypotheses:

- the split rank-one statement `SplitRankOneParabolicRationalOrbitHeightBoundStatement`
  (`AdelicSplitRankOneOrbitHeightBound`), and
- an adelic parabolic Iwasawa input: either the full
  `AdelicGroupPoints.ParabolicIwasawaStatement`, or only its finite-place part
  `FinitePlaceGroupPoints.ParabolicIwasawaStatement`.

The module proves neither hypothesis. It introduces no definitions.

## Theorems

`AdelicSiegelFactors.HasWeakChamberReduction.hasRightAdelicFundamentalSet`. Fix an
actual algebraic Siegel setup `IsSiegelAlgebraicSetup F G T i ν T₀ j` and a subgroup
`K` of `G(𝔸_F)` that is compact. If `HasWeakChamberReduction F G T i ν T₀ j K` holds,
then `HasRightAdelicFundamentalSet F G T i ν` holds. Only compactness of `K` is used,
not maximality or the Iwasawa covering.

The weak chamber reduction gives a threshold `t` such that for every
`g ∈ G(𝔸_F)¹` there are `q ∈ G(F)`, `n ∈ N(𝔸_F)`, `m ∈ M(𝔸_F)¹`, a positive point
`a` of `T₀` with `t ≤ |α(a)|` for every simple relative root `α`, and `k ∈ K` with

`ι_N(n) · ι_M(m) · positiveMap(a) · k = rational(q) · g`.

Here `N`, `M` and `P` are the unipotent radical, Levi factor and minimal standard
parabolic for `∅`. The proof applies this to `g⁻¹` and inverts:

- The compact set is `C = K`, viewed inside `G(𝔸_F)¹`. Compact subgroups lie in the
  norm-one subgroup (`compactSubgroup_le_normOneSubgroup`), and `C` is compact because
  its image under the subtype embedding is `K`.
- The positive unit is `c = t⁻¹`.
- The torus factor is `s = (j(a))⁻¹ ∈ T(𝔸_F)`, so `i(s) = positiveMap(a)⁻¹`. It lies in
  `G(𝔸_F)¹` (`positiveMap_mem_normOne`). For every simple relative root `α`,
  `|α(s)| = |α(j(a))|⁻¹ ≤ t⁻¹` (`PositiveRealTorus.normCharacter_pullback`).
- The parabolic factor is `p = ι_{M→P}(m⁻¹) · ι_{N→P}(n⁻¹) ∈ P(𝔸_F)¹`. The Levi factor
  is norm one because adelic point maps preserve norm-one subgroups
  (`map_normOneSubgroup_le`). The unipotent factor is norm one because characters of
  `P` are trivial along the unipotent `N` (`charactersTrivialAlong_of_isUnipotent`).
  Its image in `G` is `ι_M(m)⁻¹ · ι_N(n)⁻¹`.
- The rational factor is `q`, and the compact factor is `k⁻¹`.

Inverting the factorization of `g⁻¹` gives
`k⁻¹ · i(s) · ι_P(p) · rational(q) = g`, which is the required right factorization.

`AdelicSiegelFactors.splitAdelicFundamentalSet_of_splitRankOne_of_iwasawa`:

`SplitRankOneParabolicRationalOrbitHeightBoundStatement.{u} →
AdelicGroupPoints.ParabolicIwasawaStatement.{u} →
SplitAdelicFundamentalSetStatement.{u}`.

For a split setup, the Iwasawa statement applied to the minimal standard parabolic
(a parabolic subgroup by the setup) gives a parabolic Iwasawa compact `K`.
`hasWeakChamberReduction_of_splitRankOne_height` (`AdelicSplitChamberReduction`) gives
the weak chamber reduction for `K`, and the previous theorem converts it.

`AdelicSiegelFactors.splitAdelicFundamentalSet_of_splitRankOne_of_finitePlaceIwasawa`:

`SplitRankOneParabolicRationalOrbitHeightBoundStatement.{u} →
FinitePlaceGroupPoints.ParabolicIwasawaStatement.{u} →
SplitAdelicFundamentalSetStatement.{u}`.

The adelic Iwasawa statement is obtained from the published
`parabolicIwasawaStatement_of_archimedean_finite_integral`
(`AdelicIwasawaReduction`). Its archimedean input is the published theorem
`InfinitePlaceGroupPoints.parabolicIwasawaStatement`. Its integral input is the
published theorem `IntegralIwasawaFamily.existenceStatement`. So the only unproved
Iwasawa input is the finite-place statement.

## Provenance

The result is a conditional form of Springer, *Reduction theory over global fields*
(1994), property (F) for split groups (§2.1 and §§3.2–3.3), in the Library's
formulation `SplitAdelicFundamentalSetStatement`. Springer obtains the fundamental set
from the Iwasawa decomposition `G(𝔸) = P(𝔸)·K` and a bound on the torus part of the
parabolic factor. The inversion step above is the same bookkeeping as the published
`HasRightAdelicFundamentalSet.hasLeft`, in the opposite direction.
