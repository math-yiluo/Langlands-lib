# Torsion density from the cube pullback identity and ample existence

Author: Worker 3376. This internal supporting unit defines
`Langlands.AbelianScheme.Tate.FieldTwoPowerTorsionDensityReductionStatement`
and proves it as `fieldTwoPowerTorsionDensity_reduction`. It keeps two published
propositions as antecedents and does not prove the unconditional
`FieldTwoPowerTorsionDensityStatement`.

## Statement

At universe `u`, `FieldTwoPowerTorsionDensityReductionStatement.{u}` is the
implication

```text
GroupScheme.FieldCubePullbackStatement.{u} →
GroupScheme.AlgebraicallyClosedFieldAmpleExistenceStatement.{u} →
FieldTwoPowerTorsionDensityStatement.{u}
```

The conclusion is the existing closed `FieldTwoPowerTorsionDensityStatement.{u}`,
unchanged: for every algebraically closed field `Ω` of characteristic zero in
`Type u` and every actual abelian scheme `A` over `Spec Ω`, the set
`twoPowerTorsionLocus A` is dense in the underlying space of `A`.

The two antecedents are the published propositions:

- `GroupScheme.FieldCubePullbackStatement.{u}`: the balanced cube pullback
  identity for actual line bundles on commutative smooth proper geometrically
  connected group schemes over a field (proof task 815).
- `GroupScheme.AlgebraicallyClosedFieldAmpleExistenceStatement.{u}`: every
  such group scheme over an algebraically closed field has an actual ample
  line bundle (proof task 1918).

Their proofs are separate obligations. Publishing this reduction does not
complete the density proof task.

## Auxiliary results

- `exists_hasRelativeDimension`: every actual abelian scheme `A` over a field
  satisfies `A.HasRelativeDimension g` for some `g`. The source of `A` is
  connected by `GeometricallyConnected.connectedSpace_of_subsingleton`, and the
  published `smoothConnectedRelativeDimension` then gives one relative
  dimension for the smooth structure morphism. No antecedent is used.
- `natCard_level_eq_of_cubePullback_of_ample`: over an algebraically closed
  field, assuming the two antecedents, if `A` has relative dimension `g` and
  the natural number `k` is nonzero in the field, the actual torsion level
  `GroupScheme.Tate.Level A.toGrp (Over.mk (𝟙 _)) k` has `k ^ (2 * g)`
  elements. The ample antecedent, applied to `A.toGrp`, gives an ample line
  bundle `H`. The source of `A` is nonempty because it is connected. At any
  point `y`, the published `natCard_level_eq_multiplicationFinrank`
  (separably closed fields) identifies the cardinality with the rank of
  multiplication by `k` at `y`. The published
  `finrank_multiplication_eq_of_ne_zero`, which takes the cube antecedent,
  the dimension and `H` as inputs, computes this rank as `k ^ (2 * g)`.

## Proof

Fix `Ω` and `A`.

1. **Closure as an abelian subvariety.** The published
   `twoPowerTorsionClosureAbelianScheme_exists` gives an actual abelian scheme
   `B` over `Spec Ω` and a homomorphism `f : B ⟶ A` whose underlying morphism
   is a closed immersion with range `closure (twoPowerTorsionLocus A)`.
2. **Dimensions.** `exists_hasRelativeDimension` gives relative dimensions
   `gA` of `A` and `gB` of `B`.
3. **Counting `2`-torsion.** Since `Ω` has characteristic zero, `2 ≠ 0` in
   `Ω`. `natCard_level_eq_of_cubePullback_of_ample` at `k = 2 ^ 1` gives
   `2 ^ (2 * gA)` actual `2`-torsion sections of `A` and `2 ^ (2 * gB)` of
   `B`.
4. **Comparison of levels.** The range of `f` contains the torsion locus, which
   lies in its closure. So the published `twoPowerTorsionLevelComparison` at
   `n = 1` says that the level map from the `2`-torsion of `B` to that of `A`
   is bijective. Equating cardinalities gives
   `2 ^ (2 * gB) = 2 ^ (2 * gA)`, so `gB = gA` by injectivity of powers of
   two.
5. **Equality.** The published `fieldEqualDimensionClosedImmersion` shows that
   the underlying morphism of `f`, a closed immersion between abelian schemes
   of the same relative dimension, is an isomorphism. It is therefore
   surjective. So the closure of the torsion locus, which is the range of `f`,
   is the whole space, and the locus is dense.

No hypothesis is added beyond the two named antecedents. Arbitrary universe
`u` is kept. Each theorem in the file uses only the axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Provenance

The provenance is internal. This file composes the named published interfaces.
The original argument is Edixhoven, van der Geer and Moonen, *Abelian
Varieties*, preliminary version, Chapter V, §3, Theorem (5.30) and its proof
in the case `p ≠ char(k)`, printed page 84 (PDF page 88), registered as
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`. There the
Zariski closure `Y` of the `p`-power torsion is shown to be a subgroup scheme.
Its identity component `Y⁰` has `p ^ (2 m h)` points of order dividing `p ^ m`
by Prop. (5.9), where `h = dim Y⁰`, so `Y` has at most `N · p ^ (2 m h)` such
points, where `N` is its number of components. Since `Y` contains all
`p ^ (2 m g)` of them, `h = g` and `Y⁰ = X`.

The implementation differs in three points:

- The published closure result already realizes the closure as a connected
  abelian subvariety `B`, so there is no component count and the case `m = 1`
  suffices.
- The torsion count of Prop. (5.9) is replaced by the published rank formula
  `finrank_multiplication_eq_of_ne_zero`. This formula needs the cube pullback
  identity and an ample line bundle, which are the two antecedents here. The
  ample bundle on `B` is obtained by applying the ample antecedent to `B`
  itself.
- The conclusion `h = g ⇒ Y⁰ = X` is the published
  `fieldEqualDimensionClosedImmersion`.
