# Intrinsic positive-real subgroups of actual adelic tori

Worker 112.

This is an internal construction derived from
`Langlands.Global.PositiveRealTorus` and the published group-scheme point and
character APIs. The preceding module realizes the fixed-splitting construction
of Mœglin–Waldspurger I.2.1. This module proves an intrinsic description of that
subgroup and supplies its image in an actual ambient group scheme. It does not
attribute the character criterion or the following proofs to a separate
assertion in the literature.

For an arbitrary number field `F` and an actual commutative group scheme `T`
over `Spec F`, `intrinsicSubgroup F T` consists of the actual adelic points
whose every algebraic character takes values in the scalar-positive idele
subgroup. It is the intersection of the inverse images of that scalar subgroup
under the actual character homomorphisms. This definition needs no splitting.
For a nonsplit group it makes only the stated character-based construction;
this module identifies it with the positive-real coordinate subgroup only when
an actual split-torus isomorphism is supplied.

`pointMap` is the existing natural map on actual affine point groups induced
by a group-scheme homomorphism. `characterHom` composes that map with the
published affine-point equivalence for the multiplicative group. Its value is
definitionally the existing `Lie.characterValue`. `scalarSubgroup` is exactly
the range of `PositiveRealIdeles.full F`.

For a supplied finite splitting `e`, `coordinateCharacter` composes `e.hom`
with an actual coordinate projection to the multiplicative group. Its
evaluation is the corresponding coordinate under `coordinates`.
The proved monomial formula shows that every point in `subgroup F I T e`
satisfies the character criterion. Conversely, apply that criterion to the
coordinate characters and choose the resulting positive real units in each
coordinate. Injectivity of the actual affine-point equivalence shows that
their image under `full` is the given point. This proves
`subgroup_eq_intrinsicSubgroup`, and hence `subgroup_eq_of_splittings` even
when the two supplied finite index types differ. Empty index types are allowed;
the same proof applies to rank zero.

`map_intrinsicSubgroup_le` proves that an actual homomorphism of commutative
group schemes preserves the intrinsic subgroups. A target character pulls back
to a source character, and the published character-composition formula
identifies their values. No splitness is needed for this containment.

For any actual ambient group scheme `G` and homomorphism `i : T.toGrp ⟶ G`,
`imageSubgroup` is the group-theoretic image of the intrinsic subgroup under
the actual map on adelic points. `imageSubgroup_eq_map` identifies it with the
image of the coordinate construction whenever a splitting is supplied.
The map `i` is supplied and need not be an immersion or central. No central or
maximal split torus is selected, and no claim is made that characters of a
nonsplit group detect all its points.

These are algebraic statements about the actual point carriers. No topology,
closedness, Haar measure, split-centre decomposition, root system or reduction
theorem is asserted.
