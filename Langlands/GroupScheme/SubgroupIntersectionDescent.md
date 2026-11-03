# Subgroup intersections over a field and over its algebraic closure

Author: Worker 1240.

Module `Langlands.GroupScheme.SubgroupIntersectionDescent`. It is derived infrastructure for
`Langlands.GroupScheme.ParabolicIntersectionGeometryStatement` (task
`7c372114-27b9-49eb-8f69-5b1df15fbbca`). That statement asks for smoothness of a
group-scheme pullback `pullback j j'` over a field `k` and connectedness of its base change
to `AlgebraicClosure k`. Geometric arguments produce these facts for the pullback of the
base-changed maps instead. This module transfers them back.

Throughout, `k` is a field, `j : P ⟶ G` and `j' : P' ⟶ G` are arbitrary homomorphisms of
group schemes over `Spec k`, and `bc` is `GroupScheme.baseChange (toAlgebraicClosure k)`.
No closedness, smoothness or reductivity hypothesis is needed.

## Contents

- `subgroupIntersectionBaseChangeIso_inv_ι` (with a `reassoc` form). Over any base `S` and
  for any `b : S' ⟶ S`, the inverse of the comparison isomorphism
  `subgroupIntersectionBaseChangeIso b j j'` followed by the base change of
  `subgroupIntersectionHom j j'` is `subgroupIntersectionHom` of the base-changed maps. It
  follows from the Library lemma `subgroupIntersectionBaseChangeIso_hom_ι` by cancelling the
  isomorphism. A homomorphism into the base-changed pullback therefore gives one into the base
  change of the pullback with the same composite into `bc.obj G`.
- `smooth_pullback_of_smooth_pullback_baseChange`. If
  `pullback (bc.map j) (bc.map j')` is smooth over `AlgebraicClosure k`, then
  `pullback j j'` is smooth over `k`. Proof: `smooth_of_over_iso` along the comparison
  isomorphism makes `bc.obj (pullback j j')` smooth. This object's structure morphism is the
  second projection of the pullback of the structure morphism of `pullback j j'` along
  `toAlgebraicClosure k`. That map is surjective, flat and quasi-compact
  (`fieldExtension_fpqc`), and smoothness descends along such maps
  (`MorphismProperty.of_pullback_snd_of_descendsAlong` from Mathlib's flat descent).
- `connectedSpace_baseChange_pullback`. If the underlying space of
  `pullback (bc.map j) (bc.map j')` is connected, so is that of `bc.obj (pullback j j')`. The
  comparison isomorphism induces a homeomorphism of underlying spaces (`Scheme.homeoOfIso`).

## Provenance

This module is derived, not a statement from a source. It is formal: base change commutes with
pullbacks (`subgroupIntersectionBaseChangeIso`), and smoothness descends along the
faithfully flat quasi-compact morphism `Spec (AlgebraicClosure k) ⟶ Spec k`.
