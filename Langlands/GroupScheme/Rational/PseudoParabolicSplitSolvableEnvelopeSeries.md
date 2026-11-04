# Split solvability of a split torus acting on a split unipotent group

This internal derived unit gives the split solvability half of the subgroup
`S ⋉ R_us,k(P)` used in the proof of CGP Theorem C.2.5. It contains two
results over an arbitrary field `k` in an arbitrary universe `u`.

`AutomorphicAction.isSolvableScheme_of_comm` shows that the underlying group
scheme `S.toGrp` of a commutative group scheme `S` over `k` is uniformly
solvable in the all-test sense `RelativeRoot.IsSolvableScheme`. The bound is
`1`. Every point group `T ⟶ S.toGrp.X` is commutative under Mathlib's
`Hom.commGroup`, so its first derived subgroup, the commutator subgroup, is
trivial.

`AutomorphicAction.isSplitSolvableGroupScheme_semidirectProduct` concerns an
arbitrary actual action `a : AutomorphicAction S.toGrp U` of a split torus
`S.toGrp` on a smooth affine group `U` over `k`. Here `U.X.left` is connected
and `U` is split unipotent in the existing sense `RelativeRoot.IsSplitUnipotent`.
The Library semidirect product `a.semidirectProduct` then satisfies the full
existing predicate `IsSplitSolvableGroupScheme`. Its underlying scheme is the
fibre product `U × S` over `Spec k`.

The proof applies
`IsSplitSolvableGroupScheme.of_splitUnipotent_kernel_splitTorus_quotient` to
the normal-factor inclusion `a.semidirectInl : U ⟶ a.semidirectProduct` and
the projection `a.semidirectProjection : a.semidirectProduct ⟶ S.toGrp`. It
supplies the hypotheses of that theorem as follows.

- Smoothness and affineness of the product come from the existing instances
  `semidirectProduct_smooth` and `semidirectProduct_isAffineHom`. The torus
  inputs are `IsSplitTorus.smooth` and `IsSplitTorus.isAffineHom`.
- Connectedness of the product: `U` is geometrically connected by
  `geometricallyConnected_of_connected`, and its structure map is smooth,
  hence universally open. The torus is connected by
  `IsSplitTorus.connectedSpace`. Mathlib's connectedness instance for such a
  fibre product applies.
- `a.isClosedSubgroup_semidirectInl` shows that the inclusion is closed.
  This uses separatedness of the torus over the field, which is `fieldSeparated`.
- The projection is an fppf quotient with kernel range equal to the range of
  the inclusion. Its underlying morphism is the second fibre-product
  projection, by `semidirectProjection_hom`. Flatness, surjectivity and local
  finite presentation are base changes of the same properties of the
  structure map of `U`. That map is smooth, and surjective because it is
  geometrically connected. Both kernel range membership conditions say that
  the projection of a point is the identity. They agree by
  `mem_range_kernelι_iff` and `mem_range_semidirectInl_iff`.
- Geometric-point solvability: `RelativeRoot.isSolvableScheme_semidirect`
  combines the commutative bound above with
  `RelativeRoot.IsSplitUnipotent.isSolvableScheme` for `U`.
  `IsSolvableScheme.isSolvableGroupScheme` then converts uniform all-test
  solvability to the predicate `IsSolvableGroupScheme`.
- The kernel is split unipotent by hypothesis, and the quotient is the given
  split torus.

Provenance: the proof of CGP Theorem C.2.5 (Borel–Tits, printed p. 595)
asserts that the smooth connected solvable `k`-subgroup `S ⋉ R_us,k(P)` is
`k`-split. This is the standard fact that an extension of a split torus by a
split unipotent group is split solvable.
This unit proves only the special case of an actual semidirect product.
It makes no claim about the comparison of this product with any subgroup of a
pseudo-parabolic subgroup, and does not prove
`PseudoParabolicSplitSolvableEnvelopeStatement`.
