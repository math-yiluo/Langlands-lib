# The non-maximality Borel fields after a field extension

Worker 1498.

This helper module proves the four fields of `IsBorelSubgroup` other than maximality
for the base change of a Borel inclusion along an arbitrary morphism of field spectra
`b : Spec K ⟶ Spec k`. It is used by the proof of
`Langlands.GroupScheme.BorelAlgClosedFieldExtensionStatement`, where `b` is
`Spec.map (CommRingCat.ofHom (algebraMap k K))`. None of these lemmas assumes that
`k` or `K` is algebraically closed, that the extension is algebraic or separable, or
that `G` is smooth or connected. Throughout, `i : B ⟶ G` is a morphism of group schemes
over `Spec k` and the base change is the Library's `GroupScheme.baseChange b`.

## Declarations

- `BorelFieldExtension.isAffineHom_source`: if `G.X.hom` is affine and `i` is a closed
  subgroup inclusion, then `B.X.hom` is affine. Proof: the structure morphism of `B` is
  the composite of the closed immersion `i.hom.hom.left` with `G.X.hom` (`Over.w`);
  closed immersions are affine, and affine morphisms are stable under composition.
- `BorelFieldExtension.isClosedSubgroup_baseChange`: for a Borel inclusion `i`, the
  base-changed inclusion `(GroupScheme.baseChange b).map i` is a closed subgroup inclusion.
  This is the published `IsClosedSubgroup.baseChange` applied to the closed-subgroup field.
- `BorelFieldExtension.smooth_baseChange`: the structure morphism of the base change of `B`
  is by definition `pullback.snd B.X.hom b`, and smoothness is stable under base change.
- `BorelFieldExtension.connectedSpace_baseChange`: if `G.X.hom` is affine, the base change
  of `B` is connected. The subgroup `B` is smooth, connected and (by the first lemma)
  affine over `k`, so the published
  `GroupScheme.connectedSpace_baseChange_of_smooth_affine` applies. That theorem rests on
  geometric connectedness of connected group schemes of finite type over a field.
- `BorelFieldExtension.isSolvableGroupScheme_baseChange`: if `G.X.hom` is affine, the base
  change of `B` is solvable in the sense of `IsSolvableGroupScheme`, that is, the group of
  points over the chosen algebraic closure of `K` is solvable. This applies
  the published `solvableFieldExtensionStatement` (Library module
  `Langlands.GroupScheme.Absolute.SolvableFieldExtensionProof`, by Worker 1370: smooth
  affine solvable group schemes stay solvable under every field extension) to the smooth,
  affine, solvable group scheme `B`.
- `BorelFieldExtension.isBorelSubgroup_baseChange_of_maximal`: if `G.X.hom` is affine and
  `i` is a Borel inclusion, then `(GroupScheme.baseChange b).map i` is a Borel inclusion
  provided it satisfies the maximality field over `Spec K`. The hypothesis `hmax` is
  literally that field: for every group scheme `B'` over `Spec K`, every closed subgroup
  inclusion `i' : B' ⟶ G_K` with `B'` smooth, connected and solvable, and every
  `f : B_K ⟶ B'` with `f ≫ i' = i_K`, the morphism `f` is an isomorphism. The other four
  fields are the lemmas above.

The maximality field itself is not proved here. The final proof supplies it from
`BorelFieldExtension.maximal_baseChange` (module `BorelFieldExtensionMaximality`).
