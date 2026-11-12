# Renard III.3.2: subgroup restriction and the action on a fixed stalk

This pair constructs the algebraic ingredients of restriction at a point in
Renard, *Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026, III.3.2, printed p.84 / PDF p.90, the paragraph beginning
“En particulier” after the restriction functor. The source is registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

All new names have prefix `Langlands.Sheaf.Renard.SectionActions`.
They use the action sheaves of `SectionActions` and the published
`Langlands.Sheaf.Equivariant.Godement` stalk maps.

`subgroupOpens Q` keeps the actual opens of `X`, and sends a transport
arrow with label `q : Q` to the same arrow with label `(q : G)`.
`subgroupRestriction Q` precomposes an action sheaf with this functor.
Its ordinary sheaf is definitionally the original one: group labels
are restricted, and ordinary restrictions are unchanged. The identity
and composition laws follow from those of precomposition.

`stalkTransport F g x` is the published `stalkPullIso` with label `g⁻¹`.
It is the forward action from the stalk at `x` to the stalk at `g • x`.
Its source and target are the actual Mathlib stalks of the original
ordinary complex vector sheaf, defined by neighborhood colimits.
No abstract substitute stalk or transported representation is supplied
as input.

For a subgroup `Q` fixing a point `x`, `fixedStalkAction` sends
`q` to `Godement.stalkPull F.obj (q : G)⁻¹ x x`.
The inverse label is essential: published stalk pullback is
contravariant in point transport, while Renard's representation
is a left action. The action identity and multiplication laws use
the published `stalkPull_one` and `stalkPull_mul`.
`fixedStalkActions` sends a sheaf morphism to its actual map on the
original stalk. The commutation law is the published
`stalkPull_naturality`; the functor laws follow from ordinary
stalk functoriality. `fixedStalkFunctor` applies the published
`Rep.ActionToRep` conversion to obtain the same action as a Mathlib
representation.

These algebraic constructions require neither closedness of `Q`
nor local compactness of `X`. Stalk transport assumes joint
continuity of the fixed action, sufficient for the published
continuous-operator stalk construction. The group universe is
independent; the space and vector-space carriers are in `Type`,
as in `SectionActions`. Renard's topological group and locally
compact Hausdorff totally disconnected spaces are the intended
specialization.

This pair does not assert smoothness of the resulting stalk
representation and does not construct restriction to an arbitrary
locally closed subspace. In particular it is the underlying
algebraic part of his point restriction, not the complete
`R^{X,G}_{Z,Q}` functor on smooth-action categories. The general
restriction construction and its smoothness remain in this task.
