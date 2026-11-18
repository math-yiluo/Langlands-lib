# The Tits obstruction of a simply connected group

This module packages the Tits obstruction for a simply connected group. Let
`G` be an affine, locally finite type group scheme over a field `k` with
`IsSimplyConnected G`, let `K/k` be Galois (for instance a separable closure),
and let `d : GaloisPinningData k K G` be Galois pinning data. The domain is
`d.starFixedWeights` (`SimplyConnected/StarFixedWeights`): the integral weights
of the split torus `T_K` fixed by the star action of every automorphism in
`K ≃ₐ[k] K`. No condition on the action on vertices is imposed. The target is
Mathlib's matrix-stable quotient `BrauerGroup.{u,u} k` with the published
group law of `Langlands/Algebra/BrauerGroup`.

The construction follows the first assertion of Corollary 3.5 of Tits,
*Représentations linéaires irréductibles d'un groupe réductif sur un corps
quelconque*, J. reine angew. Math. 247 (1971), p. 205: the dominant
star-fixed Tits class is additive and extends to all star-fixed weights.

## Declarations

- `isStarFixedWeight_of_mem_starFixedWeights`: membership in
  `d.starFixedWeights` is the published `d.IsStarFixedWeight`
  (`mem_starFixedWeights`).
- `titsObstruction d hG : d.starFixedWeights →+ BrauerGroup.{u,u} k` is
  `titsObstructionOn` (`Reductive/TitsObstruction`) on this subgroup. The
  integral coroot span is everything by the published
  `corootSpan_eq_top_of_simplyConnected`.
- `titsObstruction_apply` unfolds it to `titsObstructionValue`.
- `titsObstruction_eq_classOf`: on a dominant star-fixed weight `λ`, the
  obstruction is `classOf (titsCSAOf ρ)` for every representation `ρ` of
  `G_K` with `IsHighestWeight ρ λ`, i.e. irreducible of highest weight `λ`.
  This is the class of the Tits algebra of the irreducible highest-weight
  representation (`Reductive/TitsDominantClass`), and it does not depend on
  the choice of such `ρ`.
- `titsObstruction_eq_sub`: for every decomposition `λ = a - b` with `a`, `b`
  dominant and star-fixed, the obstruction is `[a] - [b]`. The value does not
  depend on the auxiliary decomposition.
- `titsObstruction_eq_zero_of_mem_rootSpan`: suppose `δ` is star-fixed and,
  for every finite set `O` of simple roots, some representation of `G` over
  `k` has `δ - ∑_{i ∈ O} α_i` as a maximal weight of multiplicity one after
  scalar extension (`HasGroundMaximalWeight`). Then the obstruction vanishes
  on every star-fixed weight in the integral root span
  (`Reductive/GaloisRationalBaseChange`). The required representations, for
  `δ` the sum of the positive roots, are the subject of Task 7713.

Additivity is part of the `AddMonoidHom` structure. All characteristics are
allowed, there is no inner-type hypothesis, and the CSA representatives live
in the universe of `k`.
