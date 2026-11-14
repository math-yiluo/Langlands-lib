# The doubled-input coroot estimate from unitary rank-one coordinates

This internal module reduces `KPLocalDoubleRootCommutatorStatement` to
`QuasiSplitValuedRankOneCoordinatesStatement`. It does not prove the
coordinate statement, so it does not establish the unconditional
doubled-root estimate.

## The per-character property

`DoubledInputCommutatorProperty B hZ a` is the conclusion of
`KPLocalDoubleRootCommutatorStatement` at one character `a` of the maximal
split torus. Take a point `x` of the apartment, nontrivial
`u ∈ U_a(K)` and `u' ∈ U_{-a}(K)` with `u ∈ U_{2a}(K)` or
`u' ∈ U_{-2a}(K)`, and a positive real `r` with
`r = φ_{x,a}(u) + φ_{x,-a}(u')`. Then every factorization
`u'⁻¹ u u' u⁻¹ = v' · j(z) · v` with `v' ∈ U_{-a}(K)` and `v ∈ U_a(K)` has
`z ∈ Z(K)_{2r}` (`B.centralizerTorusFiltration hZ (2 * r)`). The groups
`U_{±2a}(K)` are `B.doubleRootGroup (±a)`, which are trivial when `±2a` is not
a relative root (KP's convention). The definition restates the statement's
hypotheses verbatim, so the final reduction is a direct application.

## Root combinatorics

- `mem_rootGroup_two_smul_of_mem_doubleRootGroup`: a point of
  `B.doubleRootGroup a` lies in the root group of the character `2 • a`. If
  `2 • a` is not a root the point is `1`.
- `two_smul_mem_relativeRoots_of_mem_doubleRootGroup`: a nontrivial point of
  `B.doubleRootGroup a` forces `2 • a` to be a relative root.
- `two_smul_mem_relativeRoots_of_two_smul_neg_mem`: if `2 • (-a)` is a
  relative root, so is `2 • a`. This uses the opposite-root property that
  `B.hasOppositeFactorPairs` supplies.
- `mem_indivisibleRoots_of_two_smul_mem`: a relative root whose double is a
  root is indivisible. If `a = m • c` for a root `c`, then
  `(2 * m) • c = 2 • a` is a root, and
  `RelativeRoot.HasOppositeFactorPairs.eq_one_or_two_of_nsmul_mem` gives
  `2 * m ∈ {1, 2}`, so `m = 1`.
- `add_eq_two_mul_of_halfTop_add_halfTop_eq`: if
  `halfTop s + halfTop t = r` in `WithTop ℝ`, then `s + t = 2r`. Both terms
  are finite because the sum is.

## The unitary computation

Fix `C : ValuedSU3RootCoordinates B hZ b` at a nonzero character `b`.
`exists_corootPoint_of_doubledInput_factorization` carries out the core
computation:

1. Choose unitary parameters `p` and `q` with `C.positive.equiv p = u` and
   `C.negative.equiv q = u'`.
2. The input in the doubled group lies in the root group of the doubled
   character, by the first combinatorial lemma. The record's `double` fields
   then show its parameter is central: `p.first = 0` or `q.first = 0`.
3. The record's depth fields identify `towerDepth p + towerDepth q` with the
   opposite value sum `φ_{x,b}(u) + φ_{x,-b}(u')`. This equals `r`, by
   `KPApartmentData.opposite_value_sum_eq`, which moves the sum from the
   record's origin to `x`. Here the tower depth is `depthA`, the half-valuation
   of the second coordinate. The halving lemma gives
   `ω(p.second) + ω(q.second) = 2r` for the extension valuation `ω`.
4. `SU3Root.oppositeProductPivot_sub_one_of_double` uses centrality to write
   `oppositeProductPivot p q - 1` as `p.second * q.second`. Hence
   `ω(t - 1) = 2r` for the pivot `t`. In particular `t ≠ 0`, since otherwise
   `ω(-1) = 0 = 2r` would contradict `r > 0`.
5. The record's `commutator_factorization` writes the commutator as a
   negative-root point, the coroot point `C.corootPoint t`, and a
   positive-root point. `centralizerComponent_eq_of_root_factorizations`
   identifies `C.corootPoint t` with the given `z`.

`ValuedSU3RootCoordinates.doubledInputCommutatorProperty` then proves
`DoubledInputCommutatorProperty B hZ b`. The unit `t` gives a rational point
`c` of the Weil restriction `T` of `𝔾_m` from the record's extension. That
`T` is a torus, and an induced torus, follows from
`WeilGm.isTorus_of_finite_separable` and
`WeilGm.isInducedTorus_of_finite_separable`.
`MaximalUnramified.weilGm_geometricCharacter_bound` turns `ω(t - 1) ≥ 2r` into
a bound on every geometric character of `T`. `mem_localTorusFiltration_of_induced`
converts these bounds into `c ∈ T(K)_{2r}`. Finally
`map_localTorusFiltration_le`, applied to the record's coroot morphism, sends
`c` to `z ∈ Z(K)_{2r}`.

## Reduction to the coordinate statement

`doubledInputCommutatorProperty_of_valuedSU3RootCoordinates` assumes a
provider of unitary records at every indivisible root `b` whose double is a
root. It proves the property at every relative root `a`. The nontrivial
doubled input makes `2 • a` a root: directly for `u`, and through the
negation lemma for `u'`. Then `a` is indivisible, and the provider's record
at `a` applies.

`kpLocalDoubleRootCommutator_of_valuedRankOneCoordinates` proves
`QuasiSplitValuedRankOneCoordinatesStatement.{u} →
KPLocalDoubleRootCommutatorStatement.{u}`. The provider is the second
component of the coordinate statement at each indivisible root. The
implication is kept as a hypothesis; this module does not assert the
coordinate statement.

## Provenance and scope

This internal module follows the computation in KP Proposition 7.1.1 and
Lemma 7.2.3 for a multipliable root. If one input is in the doubled root
group, the coroot component of the commutator has deviation from `1` of
valuation exactly twice the depth sum. Everything holds at arbitrary universe
`u`, with no characteristic restriction. The module does not use
`MaximalUnramified.LocalMoyPrasadGroupPropertiesStatement` or any of its
conclusions.
