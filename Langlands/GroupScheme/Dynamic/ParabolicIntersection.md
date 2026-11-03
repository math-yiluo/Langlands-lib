# Intersections of two dynamic parabolics

Author: Worker 1240.

Module `Langlands.GroupScheme.Dynamic.ParabolicIntersection`. It is derived infrastructure for
`Langlands.GroupScheme.ParabolicIntersectionGeometryStatement` (task
`7c372114-27b9-49eb-8f69-5b1df15fbbca`). Over an algebraic closure, two parabolics that contain
a common maximal torus are the dynamic parabolics `P_G(ν ∘ t)` and `P_G(ν' ∘ t)` of two
cocharacters of that torus. This module proves smoothness and, conditionally, connectedness of
the intersection of two such dynamic parabolics. It uses no reductive or Borel theory.

Throughout, `k` is a field and `G` is a group scheme over `Spec k` whose structure morphism is
smooth and affine. `Dynamic.parabolic χ` is the dynamic parabolic subgroup functor `P_G(χ)` of
a cocharacter `χ : 𝔾_m ⟶ G`.

## Structural input

Smoothness is unconditional. It uses the Library proof `dynamicSmooth`, which formalizes
Conrad–Gabber–Prasad, *Pseudo-reductive groups*, 2nd ed. (2015), Proposition 2.1.8(3),
printed p.53: representatives of `P_G(χ)` are smooth when `G` is smooth.

Connectedness takes `hCo : DynamicConnectedStatement` as an explicit hypothesis and does not
prove it. This is CGP Proposition 2.1.8(4), printed p.53: `P_G(χ)` has connected fibers when
`G` does. Its proof task is `91e60b81`. The hypothesis appears only on the lemmas below.

## Contents

- `smooth_connected_of_isRepresentedBy_parabolic_inf`. Let `χ, χ'` be cocharacters of `G`
  with the points of `χ'` in `P_G(χ)`. Let `c : H ⟶ G` represent the pointwise intersection
  `P_G(χ) ⊓ P_G(χ')`. Then `H` is smooth over `k`. Given `hCo`, if `G` has connected
  underlying space, so does `H`.

  Proof. Let `i : Q ⟶ G` be the closed representative `Dynamic.Affine.parabolicHom χ` of
  `P_G(χ)`. `Q` is smooth by `dynamicSmooth`, and it is affine because `i` is a closed
  immersion. By `IsRepresentedBy.liftOfLE`, `χ'` factors as `χ'_Q` through `i` and `c` factors
  as `c_Q` through `i`. As a subgroup functor `P_Q(χ'_Q)` is the preimage of `P_G(χ')` in `Q`,
  by `Dynamic.parabolic_eq_comap_of_isClosedSubgroup`. A pointwise comparison then shows that
  `c_Q` represents `P_Q(χ'_Q)`: a point of `Q` whose image lies in `P_G(χ')` also lies in
  `P_G(χ)`, so it factors through `c`, and cancelling the monomorphism `i` gives a factorization
  through `c_Q`. So `H` is a representative of a dynamic parabolic of the smooth affine group
  `Q`, and `dynamicSmooth` gives smoothness of `H`. For connectedness, `hCo` applied to `G` and
  `χ` makes `Q` connected, and `hCo` applied to `Q` and `χ'_Q` makes `H` connected.
- `range_le_parabolic_groupHom_comp`. For a commutative group scheme `T`, a homomorphism
  `t : T ⟶ G` and a cocharacter `ν` of `T`, the points of `t` lie in `P_G(ν ≫ t)`. This
  combines `range_le_centralizer_groupHom_comp` (points of `t` centralize `ν ≫ t`) with
  `Dynamic.centralizer_le_parabolic`.
- `smooth_connected_pullback_of_range_eq_parabolic`. Let `t : T ⟶ G` be as above, let
  `ν, ν'` be cocharacters of `T`, and let `i : P ⟶ G` and `i' : P' ⟶ G` be homomorphisms
  whose underlying morphisms over the base are monomorphisms, with
  `range i = P_G(ν ≫ t)` and `range i' = P_G(ν' ≫ t)`. Then the group-scheme pullback
  `pullback i i'` is smooth over `k`. Given `hCo`, it has connected underlying space if `G`
  does. Finally `t` factors through the composite `pullback.fst i i' ≫ i`.

  Proof. The pullback square `subgroupIntersection_isPullback` and the monomorphism `i'`
  make the first projection a monomorphism, so `pullback.fst i i' ≫ i` is one too. Its range is
  `range i ⊓ range i'` by `range_subgroupIntersectionHom`. Hence it represents
  `P_G(ν ≫ t) ⊓ P_G(ν' ≫ t)`. The points of `ν' ≫ t` are points of `t`
  (`SubgroupFunctor.range_comp_le`), so they lie in `P_G(ν ≫ t)` by the previous lemma. The
  first lemma then gives smoothness and connectedness. The points of `t` lie in both
  parabolics by the previous lemma, and `liftOfLE` gives the factorization.

## Provenance

This module is derived, not a statement from a source. Borel–Tits, *Groupes réductifs* (1965),
Corollary 4.5, printed p.87, proves that an intersection of two parabolics of a connected
reductive group over an algebraically closed field is connected. Their argument goes through
Levi decompositions and unipotent radicals. The present argument is the dynamic method
instead: the intersection of `P_G(χ)` and `P_G(χ')` is the dynamic parabolic of `χ'` inside
`P_G(χ)`. The functoriality step is the Library lemma
`Dynamic.parabolic_eq_comap_of_isClosedSubgroup`: for a closed subgroup `j : G' ⟶ G`, the
dynamic parabolic of a cocharacter of `G'` is the preimage of the dynamic parabolic in `G` of
its composite with `j`. Only `range χ' ≤ P_G(χ)` is used, not that `χ` and `χ'` commute.
