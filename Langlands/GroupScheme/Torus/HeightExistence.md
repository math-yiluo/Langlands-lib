# Tori are smooth and connected; maximal tori exist by coordinate-kernel height

Worker 1418.

This module reuses the elementary geometric properties of the published `IsTorus`
predicate from `Torus/Geometry`. It shows that every affine group scheme locally of finite type
over a field has a maximal torus, in the sense of the published
`IsMaximalTorus`, defined over that field. The field is arbitrary: any
characteristic, not necessarily perfect or algebraically closed. Everything
lives at universe `u`.

Everything here is derived internal content. The existence theorem plays the
role of the rational existence input to Milne, *Algebraic Groups* (2017),
Corollary 17.83 (printed p.379). The proof does not follow Milne's route. It
uses Worker 135's published finite-height machinery from
`Absolute/BorelExistence*` instead of a dimension or rank argument.

## Geometry of tori

The smoothness and connectedness results below are imported from
`Torus/Geometry`; the bundled commutative solvability lemma specializes its
`isSolvableGroupScheme_of_isCommMonObj`.

`IsTorus.smooth`: a torus `T` over `k` is smooth. By definition `T` becomes
split after base change to some extension field `K`, and published split tori
are smooth (`IsSplitTorus.smooth`). The map `Spec K ⟶ Spec k` is surjective, flat
and quasi-compact (`fieldExtension_fpqc`). Mathlib's flat-descent instance for
`Smooth` along that class then descends smoothness of the second projection of
the pullback to `T.X.hom`
(`MorphismProperty.of_pullback_snd_of_descendsAlong`).

`IsTorus.connectedSpace`: the underlying space of a torus is connected. The base
change to a splitting field is connected (`IsSplitTorus.connectedSpace`). The
first projection from the pullback to `T` is surjective, as a base change of the
surjective map `Spec K ⟶ Spec k`. A continuous surjective image of a connected
space is connected.

`CommGroupScheme.isSolvableGroupScheme`: a commutative group scheme over a field
satisfies the published `IsSolvableGroupScheme`. Its base change to an
algebraic closure is again commutative, so the group of its geometric points is
commutative and hence solvable.

## The trivial torus

`trivialSplitTorusIso S` is an isomorphism, over any base scheme `S`, between the
trivial group scheme `Grp.trivial (Over S)` and the split torus on the empty
index type `PEmpty`. It is built with the published `isoOfPointModels`: over
every test scheme both groups have exactly one point, so the two point functors
are matched by the unique multiplicative equivalence. `isSplitTorus_trivial`
records that the trivial group is a split torus. `trivialCommGroupScheme S` is
the trivial group as a `CommGroupScheme`; commutativity holds because all
morphisms into a terminal object agree.

`exists_isTorus_isClosedSubgroup`: every group scheme over a field has a closed
torus, namely the unit inclusion of the trivial group. It is a closed immersion
because it is a section of the structure morphism from a one-point scheme, as in
the published `BorelExistence.exists_admissible`.

## Existence of maximal tori

Let `G` be a group scheme over `Spec k` with `IsAffineHom G.X.hom` and
`LocallyOfFiniteType G.X.hom`. For every closed torus `i : T ⟶ G` the published
`BorelExistence.coordinateKernel i` has finite height. It needs the source to be
smooth and connected, which the results above supply.

`exists_isMaximalTorus_minimal_height` uses `Nat.find` to choose a closed torus
`i : T ⟶ G` whose coordinate kernel has the least height among all closed tori
of `G`. The theorem returns `i` together with this global height comparison. To
see that `i` satisfies `IsMaximalTorus`, let `i' : T' ⟶ G` be a closed torus and
`f : T ⟶ T'` a homomorphism with `f ≫ i' = i`. Then `T'` is smooth and
connected, and the height of the kernel of `i` is at most that of `i'`. The
published `BorelExistence.isIso_of_coordinateKernel_height_le` therefore makes
`f` an isomorphism, which is exactly the maximality clause of `IsMaximalTorus`.

`exists_isMaximalTorus` forgets the height comparison: it gives a commutative
group scheme `T` over `Spec k` and a homomorphism `i : T.toGrp ⟶ G` with
`IsMaximalTorus i`. Smooth morphisms are locally of finite type, so this applies
to every smooth affine group scheme over a field. No connectedness, smoothness,
perfectness or splitness of `G` is assumed. The module asserts nothing about
conjugacy of maximal tori, their behaviour under field extension, or
geometric maximality.
