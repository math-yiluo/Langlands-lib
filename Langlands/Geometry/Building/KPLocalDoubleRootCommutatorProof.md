# Proof of the doubled-root commutator estimate over `K = F^ur`

Module `Langlands.Geometry.Building.KPLocalDoubleRootCommutatorProof`.
Worker 131, for Task 6704.

The theorem `Langlands.Geometry.Building.kpLocalDoubleRootCommutator` proves
exactly `KPLocalDoubleRootCommutatorStatement.{u}`, at an arbitrary universe
`u`, with no added hypothesis. The statement is the doubled case of the `SU_3`
computation in the quasi-split proof of KP Proposition 7.1.1, combined with the
congruence criterion and the functoriality of the torus filtration from the
proof of KP Lemma 7.2.3. Take building data `B` over `K = F^ur` whose
centralizer `Z` is a torus. Take nontrivial `u ∈ U_a(K)` and `u' ∈ U_{-a}(K)`
with `u ∈ U_{2a}(K)` or `u' ∈ U_{-2a}(K)`, and depth
`r = φ_{x,a}(u) + φ_{x,-a}(u') > 0`. Then the `Z`-component `z` of every
factorization `u'⁻¹ u u' u⁻¹ = v' · j(z) · v` lies in `Z(K)_{2r}`.

## The proof

The proof is one application that combines two published theorems:

- `kpLocalDoubleRootCommutator_of_valuedRankOneCoordinates`, from
  `RankOneDoubledInputCoroot`, proves the implication
  `QuasiSplitValuedRankOneCoordinatesStatement.{u} →
  KPLocalDoubleRootCommutatorStatement.{u}`.
- `quasiSplitValuedRankOneCoordinates`, from
  `QuasiSplitValuedRankOneCoordinatesProof` (Task 6651), proves
  `QuasiSplitValuedRankOneCoordinatesStatement.{u}`. Every indivisible relative
  root `b` has valued `SU_3` coordinates when `2 • b` is a relative root.

## How the implication works

The implication's paired Markdown has the details. For each relative root `a`:

- A nontrivial input in `U_{±2a}(K)` forces `2 • a` to be a relative root, so
  `a` is indivisible. The coordinate statement then supplies valued `SU_3`
  coordinates at `a`.
- In those coordinates the input in the doubled group has a central
  parameter. The pivot `t` of the opposite product therefore satisfies
  `t - 1 = p.second * q.second`, whose valuation is exactly `2r`.
- The record's commutator factorization identifies `z` with the coroot image
  of `t`. The congruence `ω(t - 1) ≥ 2r` puts the corresponding point of the
  induced torus in its filtration at depth `2r`. Functoriality of the torus
  filtration along the coroot morphism then gives `z ∈ Z(K)_{2r}`.

The proof does not use `LocalMoyPrasadGroupPropertiesStatement` or any result
about it.
