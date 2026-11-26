# The real normalized adjacent-rank equation at every inducing parameter

This module removes the chamber condition from `RealAdjacentCanonicalChamber` by holomorphic
continuation in the inducing exponents, and derives the adjacent-rank character growth
`RealJacquet.RealLocalAdjacentCharacterGrowthAtRank r` from the equal-rank character growth at
rank `r`. It is the real counterpart of the Library's `ComplexAdjacentCanonical` and
`ComplexAdjacentFromEqualGrowth`. Write `H = GL_(r+1)(ℝ)` and `gap` for `r < r + 1`.

## The determinant sign of a character list

- `charData_character_neg_one`: the value at `−1` of the character `charData e t` is `(−1)^e`
  and does not depend on `t`.
- `determinant_characterList_neg_one`: consequently
  `det(characterList p z, −1) = det(characterList p z', −1)` for all exponent tuples `z`, `z'`.

## Removing the chamber condition

- `cons_mem_realSpectralChamber`: if `q` is in the strict chamber `realSpectralChamber n` and
  `Re q₀ < Re x`, then `Fin.cons x q` is in `realSpectralChamber (n+1)`.
- `realChamberRemoval`. Let `A` be a property of exponent tuples `Z : Fin (n+2) → ℂ` such that
  1. for every holomorphic family `p : ℂ → Fin (n+2) → ℂ`, if `A (p z)` holds on a disk about `0`
     then `A (p 1)` holds, and
  2. for every tail `q` there is `M` such that `A Z` holds whenever `Fin.tail Z = q`, `Z` is in the
     strict chamber and `M ≤ Re Z₀`.
  Then `A Z` holds for every `Z`.

  Proof. First fix a tail `q` in the strict chamber and any leading exponent `x`. On the line
  `u(z) = x₀ + z (x − x₀)` from a real `x₀` larger than `Re q₀` and `M`, the tuples `Fin.cons (u z) q`
  satisfy the conditions of 2 for `z` near `0`, so 1 gives `A (Fin.cons x q)`. For a general `Z`,
  take the line from `p₀ = (0, −1, −2, …)`, whose tail is in the strict chamber, to `Z`. The tail
  stays in the open chamber near `0`, so the first step gives `A` there, and 1 gives `A Z`.

## The equation for canonical values

`realAdjacentCanonicalGrowth`: assume `RealOrthogonalCompactProjectionPremise r` and
`RealLocalEqualCharacterGrowthAtRank r`. Let `a ∈ ℝˣ`, parities `P : Fin (r+2) → Fin 2`, a list `fs`
of `r+1` character data with block list `es`, a uniform real Whittaker map `B` of character `−a` on
the compact-finite standard module of `es`, and a vector `v`. Then for every exponent tuple `Z`,
`RealUnequalFamily.HasRealUnequalCanonicalPairGrowth gap a a (−a) D P Z es √|a| _ sign (B v)` holds
with `sign = det(characterList P 0, −1)^(r+1) · det(es, −1)`: for every vector `f` of the standard
module of `characterList P Z`, the pair `realUnequalIntegral gap D W (B v)`,
`realUnequalDualIntegral gap a D W (B v)` with `W = canonicalJacquetMap (−a) P Z f` satisfies
`HasRealPairNormalizedGrowth` for `characterList P Z × es` and their duals with parameter `−a`,
scale `√|a|` and that sign.

Proof. Apply `realChamberRemoval`. The continuation property 1 is
`RealUnequalFamily.realUnequalCanonicalGrowthReflection`, for the fixed function `B v`, which is
regular of character `−a` with polynomial derivative growth (`realUniformWhittakerRegularity`); the
sign is a product of units, hence nonzero. For 2, given a tail `q`, take for `M` an upper bound of
the finitely many numbers
`(r+1) + normExponent (realPositionExponent (characterList (Fin.tail P) q)) (r+1) i − (r+2)/2`; then `M ≤ Re Z₀` gives the
Godement bound of `realAdjacentCanonicalChamberGrowth`, which is applied with the parameter `−a`.
Its conclusion is rewritten with `−(−a) = a`, `√|−a| = √|a|` and
`determinant_characterList_neg_one`.

## Adjacent-rank growth from equal-rank growth

`RealAdjacentFromEqualGrowthStatement r` is the implication
`RealGodement.RealUniformCanonicalRangePremise → RealOrthogonalCompactProjectionPremise r →
RealLocalEqualCharacterGrowthAtRank r → RealLocalAdjacentCharacterGrowthAtRank r`.
`realAdjacentFromEqualGrowth` proves it for every `r`. Given character lists `ds` of rank `r+2` and
`es` of rank `r+1`, write them as `characterList P Zs` and `characterList P' Zs'`
(`RealGodement.exists_characterList_eq`). The canonical range premise writes `W` in the model of
`ds` with character `a` as `canonicalJacquetMap (−a) P Zs F`, and `W'` in the model of `es` with
character `−a` as `canonicalJacquetMap a P' Zs' F'`, a value of a uniform Whittaker map of
character `−a`. `realAdjacentCanonicalGrowth` at `Z = Zs`, followed by
`determinant_characterList_neg_one`, is the required normalized equation with sign
`det(ds, −1)^(r+1) · det(es, −1)`.

## Relation to the literature

H. Jacquet, *Archimedean Rankin–Selberg integrals* (2009), registered as
`jacquet-2009-archimedean-rankin-selberg`, §8.3, pp. 58–60, proves Theorem 2.1 for the pair
`(n, n − 1)` from the pair `(n − 1, n − 1)`. In §8.1, pp. 53–54, both sides of the identities are
entire functions of the inducing exponents for holomorphic standard families, so it suffices to
prove them on an open set of exponents. There Jacquet uses Godement sections with standard
Schwartz tests, which span the compact-finite vectors in the convergence range (7.2) by
Proposition 7.1(vi), p. 43. Proposition 7.1(iii) and (v) gives the wider finite-sum spanning at
every inducing tuple, with tests compactly supported in the full-rank locus. The formal proof
likewise establishes the equation in its chamber, where the Library's Gaussian spanning theorem
applies, and reaches all inducing parameters with the Library's reflection theorem for
holomorphic families of canonical values. The identification of every
element of a uniform model with a canonical value, and the compact projection along the
orthogonal group, are hypotheses of `RealAdjacentFromEqualGrowthStatement`; this module does not
prove them. The module `RealOrthogonalCompactProjection` proves the compact projection premise at
every rank, and `RealLocalPositiveEqualReduction` combines this module with the equal-rank step
`RealGodement.realLocalEqualGrowthStep` in an induction on the rank.
