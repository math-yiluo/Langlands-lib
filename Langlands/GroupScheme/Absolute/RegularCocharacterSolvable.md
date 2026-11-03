# Solvability of closed subgroups representing dynamic parabolic subgroups

Worker 303. This module provides the solvability step of clause 1 of
`Langlands.GroupScheme.RegularCocharacterBorelStatement` (proof task
`618cd683-cfcd-43a3-b4bf-6c8abd208b1f`). It concerns a closed subgroup
`i : B ⟶ G` representing the dynamic parabolic subgroup functor `P(χ)` of a
cocharacter. The module proves that `B` is solvable in the published sense
`IsSolvableGroupScheme` as soon as the dynamic centralizer `Z(χ)` lies in the
range of a homomorphism from a commutative group scheme.

## Points over an algebraic closure

`algebraicClosurePoint k` is the test scheme `Spec k̄ → Spec k`. It is the
image under `Over.map (toAlgebraicClosure k)` of the identity of
`Spec k̄`.

- `isSolvableGroupScheme_of_isSolvable_points`: if the points of `H` over
  `algebraicClosurePoint k` form a solvable group, then
  `IsSolvableGroupScheme H`. The published `IsSolvableGroupScheme` asks for
  solvability of the points of the base change `H_{k̄}` over `Spec k̄`. The
  published multiplicative pullback adjunction `baseChangePointsEquiv`
  identifies these with the points of `H` over `Spec k̄ → Spec k`. This is
  the argument used in the published `GeneralLinearBorelProof`.
- `isSolvable_points_of_isRepresentedBy`: if `i : B ⟶ G` represents a
  subgroup functor `F` (`SubgroupFunctor.IsRepresentedBy`), then
  `x ↦ x ≫ i` is an injective group homomorphism from the points of `B` over
  `U` into `F(U)`. Injectivity comes from the monomorphism part of
  `IsRepresentedBy`; the map lands in `F(U)` because `range i = F`. So the
  points of `B` over `U` are solvable whenever `F(U)` is.

## Parabolic subgroups

`isSolvableGroupScheme_of_isRepresentedBy_parabolic` assumes:

- `G` is affine and locally of finite type over a field `k`;
- `χ` is a cocharacter of `G`;
- `i : B ⟶ G` represents `Dynamic.parabolic χ`;
- the points of `Dynamic.centralizer χ` over `algebraicClosurePoint k` form a
  solvable group.

It concludes `IsSolvableGroupScheme B`.

The proof chains three results. `Dynamic.isSolvable_unipotent_carrier` (from
`Dynamic.UnipotentSolvable`) gives solvability of the points of `U(χ)`.
`Dynamic.isSolvable_parabolic_carrier` then gives solvability of the points of
`P(χ)`. The two lemmas above finish the argument.

- `isSolvable_centralizer_carrier_of_le_range`: if
  `Dynamic.centralizer χ ≤ SubgroupFunctor.range j` for some
  `j : T ⟶ G` with `T` a commutative group scheme, then the points of
  `Z(χ)` over every `U` commute, hence form a solvable group. Two such points
  are `a ≫ j` and `b ≫ j` with `a, b` points of `T`, and `a * b = b * a`.
- `isSolvableGroupScheme_of_isRepresentedBy_parabolic_of_le_range` combines
  the two: under the same hypotheses on `G` and `i`, with
  `Dynamic.centralizer χ ≤ SubgroupFunctor.range j` for such a `j`, `B` is
  solvable.

For a split maximal torus `j` of a connected reductive group and a regular
cocharacter `ν`, the hypothesis `Z(ν ≫ j) ≤ range j` would follow from two
published statements, `GenericCentralizerStatement` and
`MaximalTorusCentralizerStatement`. Neither is proved at the time of writing,
and neither is assumed in this module.

## Source

The solvability argument is that of Milne, *Algebraic Groups* (2017), source
ID `milne-2017-algebraic-groups`, proof of Proposition 21.29 (printed p.434,
PDF p.450). There, `Z(λ) = T` and `P(λ) = U(λ) ⋊ T` with `U(λ)` unipotent, so
`P(λ)` is solvable. Here the semidirect decomposition is used through the
published limit homomorphism, and unipotence through the solvability of the
points of `U(λ)`. The torus hypothesis enters only through the inclusion
`Z(χ) ≤ range j`.

The test object `algebraicClosurePoint` is imported from
`Absolute.AlgebraicClosurePoint`, shared with the general-linear Borel proof.
