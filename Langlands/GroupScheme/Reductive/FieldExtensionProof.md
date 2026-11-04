# Connected reductivity under arbitrary field extension: proof

Author: Worker 1359.

The theorem `Langlands.GroupScheme.connectedReductiveFieldExtensionStatement`
proves exactly the published proposition
`Langlands.GroupScheme.ConnectedReductiveFieldExtensionStatement.{u}`, imported
from `Langlands.GroupScheme.Reductive.FieldExtensionStatement`.

For arbitrary fields `k K : Type u` with `Algebra k K`, and an actual group
scheme `G` over `Spec k`, it proves that `IsConnectedReductive G` implies
`IsConnectedReductive G_K`, where

```lean
G_K = (GroupScheme.baseChange
  (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G
```

This equality specifies notation for the actual pullback. The result includes
imperfect fields, inseparable and transcendental extensions, arbitrary
characteristic, and the trivial and zero-dimensional groups. All fields and
schemes retain the statement's arbitrary universe `u`.

## Implemented proof

The proof installs the smoothness, affineness and connectedness supplied by
`IsConnectedReductive G` as local instances. Smoothness and affineness of the
pullback structure morphism follow from the existing base-change instances.
The published `GroupScheme.connectedSpace_baseChange_of_smooth_affine` in
`Langlands.GroupScheme.GeometricConnectedness` supplies connectedness of `G_K`.

For the fourth field, put
`Gbar = (GroupScheme.baseChange (toAlgebraicClosure k)).obj G`. This group is
smooth and affine by base change, connected by
`IsConnectedReductive.connectedSpace_toAlgebraicClosure`, and has trivial
unipotent radical by the hypothesis's geometric-radical field.

The published `algebraicClosureEmbedding k K` equips `AlgebraicClosure K` with
an algebra structure over `AlgebraicClosure k`. Apply the unconditional theorem
`algebraicallyClosedRadicalFieldExtensionStatement` from
`Langlands.GroupScheme.Reductive.RadicalFieldExtensionProof` to these two
algebraically closed fields and `Gbar`. It gives a trivial unipotent radical
after this extension.

The published natural isomorphism `algebraicClosureBaseChangeIso k K` compares
this iterated pullback with the pullback of `G_K` to `AlgebraicClosure K`.
Its scalar compatibility is built into the comparison, and the base map for
the local algebra structure is definitionally the comparison's base map.
Apply `HasTrivialUnipotentRadical.of_iso` from
`Langlands.GroupScheme.Reductive.GeneralLinear` to the inverse comparison.
This proves the geometric-radical field of `IsConnectedReductive G_K`.

## Provenance and dependencies

This is derived proof assembly from the published radical-preservation,
geometric-connectedness, closure-comparison and isomorphism-transport results.
Every input is a proved Library theorem; the final theorem has no additional
premise. The statement's Markdown records its correspondence with the forward
direction of Milne, *Algebraic Groups* (2017), Proposition 19.13, and Conrad,
*Reductive group schemes* (2014), p.81 and Exercise 3.4.1. The substantive
algebraically closed extension argument is implemented and documented in
`RadicalFieldExtensionProof` and its helpers. The present module supplies the
remaining comparison between the two chosen algebraic closures.

The proof retains the existing `IsConnectedReductive`,
`HasTrivialUnipotentRadical`, and `GroupScheme.baseChange` definitions. In
particular, the radical conclusion is equality of subgroup functors on all
test schemes, as required by the original predicate. The proof uses no
parabolic preservation or `ParabolicDynamicStatement` result.
