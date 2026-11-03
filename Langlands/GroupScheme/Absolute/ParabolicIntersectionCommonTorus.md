# Parabolic pairs from a common maximal torus and the two-parabolic geometry

Author: Worker 1240.

Module `Langlands.GroupScheme.Absolute.ParabolicIntersectionCommonTorus`. It defines one
predicate, `IsCommonTorusParabolicPair`, and proves a conditional reduction for
`Langlands.GroupScheme.ParabolicIntersectionGeometryStatement.{u}` (task
`7c372114-27b9-49eb-8f69-5b1df15fbbca`). It does not prove that statement.

## The predicate

`IsCommonTorusParabolicPair j j'` is defined for a field `K : Type u`, group schemes
`G, P, P'` over `Spec K` and homomorphisms `j : P ⟶ G`, `j' : P' ⟶ G`. It holds when there are
a commutative group scheme `T` over `Spec K`, a homomorphism `t : T ⟶ G` with
`IsMaximalTorus t`, and cocharacters `ν, ν'` of `T` such that

- `SubgroupFunctor.range j = Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ t)`, and
- `SubgroupFunctor.range j' = Dynamic.parabolic (CommGroupScheme.groupHom ν' ≫ t)`.

So the subgroup functors of points of `j` and `j'` are the dynamic parabolics `P(ν ≫ t)` and
`P(ν' ≫ t)` of two cocharacters of one maximal torus of `G`. The definition places no
condition on `G`, `j` or `j'`, and asserts no existence. It names the data that the
classical argument produces over an algebraically closed field (see below), so the reduction
can state that input in one line.

## The reduction

`parabolicIntersectionGeometry_of_commonTorus hCo hTorus :
ParabolicIntersectionGeometryStatement.{u}` takes two explicit hypotheses.

- `hCo : DynamicConnectedStatement.{u}`. This is Conrad–Gabber–Prasad, *Pseudo-reductive
  groups*, 2nd ed. (2015), Proposition 2.1.8(4), printed p.53: dynamic parabolics of a
  smooth connected affine group over a field are connected. Its proof task is `91e60b81`.
- `hTorus`, the common-torus input. For every field `k : Type u`, connected reductive `G` over
  `k` and parabolic subgroups `j : P ⟶ G`, `j' : P' ⟶ G`, it asserts
  `IsCommonTorusParabolicPair (bc.map j) (bc.map j')`, where
  `bc = GroupScheme.baseChange (toAlgebraicClosure k)`.

`hTorus` is the Borel–torus side of the classical argument. Over an algebraically closed
field, the parabolics `P_K` and `P'_K` contain Borel subgroups, and two Borel subgroups contain
a common maximal torus (Borel–Tits, *Groupes réductifs* (1965), §2.4, printed p.65). That
torus is split, and a parabolic containing a split maximal torus is the dynamic parabolic of a
cocharacter of it (the published `SplitParabolicCocharacterStatement`, task `747d4756`). This
module does not prove `hTorus`. Both hypotheses appear only on this theorem.

## Proof

Fix `k`, `G`, `j`, `j'`. Unfolding `IsCommonTorusParabolicPair` in `hTorus` gives `T`, `t`,
`ν`, `ν'`, maximality of `t` and the two range equations. Write `H = pullback j j'` and
`c = pullback.fst j j' ≫ j`.

1. Parabolic subgroups are closed subgroups, so `c` represents `range j ⊓ range j'`
   (`isRepresentedBy_subgroupIntersectionHom`). Representability, ranges and pointwise
   intersections commute with base change (`IsRepresentedBy.baseChange`,
   `SubgroupFunctor.inf_baseChange`, `SubgroupFunctor.range_baseChangeHom`). By the two range
   equations, `bc.map c` therefore represents `P(ν ≫ t) ⊓ P(ν' ≫ t)`.
2. `bc.obj G` is smooth and affine, by base change from `G`. The points of `ν' ≫ t` are points
   of `t`, so they lie in `P(ν ≫ t)` (`range_le_parabolic_groupHom_comp`). Then
   `smooth_connected_of_isRepresentedBy_parabolic_inf` from
   `Langlands.GroupScheme.Dynamic.ParabolicIntersection` makes `bc.obj H` smooth. Given `hCo`
   and the connectedness of `bc.obj G` (`IsConnectedReductive.connectedSpace_toAlgebraicClosure`),
   it also makes `bc.obj H` connected. This is the second clause of the target.
3. Smoothness of `H` over `k` follows by fpqc descent of smoothness along
   `Spec (AlgebraicClosure k) ⟶ Spec k` (`fieldExtension_fpqc`,
   `MorphismProperty.of_pullback_snd_of_descendsAlong`). This is the first clause.
4. The points of `t` lie in both `P(ν ≫ t)` and `P(ν' ≫ t)`
   (`range_le_parabolic_groupHom_comp`). So `t` factors as `f ≫ bc.map c` with
   `f : T ⟶ bc.obj H` (`IsRepresentedBy.liftOfLE`), and `IsMaximalTorus (f ≫ bc.map c)` is
   `IsMaximalTorus t`. This is the third clause.

## Provenance

This module is derived. `IsCommonTorusParabolicPair` is an internal predicate, not a
definition from the literature. It packages the data of the classical argument described
under "The reduction". The target's sources are Borel–Tits, *Groupes réductifs* (1965),
§2.4, printed p.65 (a common maximal torus of two Borel subgroups), and Corollary 4.5,
printed p.87 (connectedness of `P ∩ P'`). The reduction keeps Borel–Tits' full-rank input in
`hTorus`, but replaces their proof of Corollary 4.5, which uses Levi decompositions and
unipotent radicals, by the dynamic description: `P ∩ P'` becomes a dynamic parabolic inside
`P(ν ≫ t)` (CGP Proposition 2.1.8(3),(4)). Smoothness of the actual scheme-theoretic pullback,
which the target requires beyond Borel–Tits' reduced setting, comes from CGP 2.1.8(3) through
the Library proof `dynamicSmooth`.
