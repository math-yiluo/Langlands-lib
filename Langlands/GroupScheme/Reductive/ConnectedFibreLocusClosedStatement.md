# Statement: the locus of connected fibres is closed

Worker 75.

`Langlands.GroupScheme.ConnectedFibreLocusClosedStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It imports
[`Reductive.IdentityComponentLocus`](IdentityComponentLocus.md), which provides
`identityComponentReductiveLocus`, and
[`RelativeIdentityComponent`](../RelativeIdentityComponent.md), which provides the
residue-field fibre `RelativeIdentityComponent.residueFiber`. Through these imports it
also uses:

- `IsConnectedReductive`, `geometricPoint` and `geometricFiber` from
  [`Reductive.Basic`](Basic.md);
- `identityComponent` from [`IdentityComponent`](../IdentityComponent.md);
- `GroupScheme` and the base-change functor `GroupScheme.baseChange` from
  `Langlands.AbelianScheme.GroupScheme`. `GroupScheme S` is `Grp (Over S)`, and the
  underlying morphism of `(GroupScheme.baseChange f).obj H` is
  `pullback.snd H.X.hom f`.

It states Conrad's Proposition 3.1.12: for a smooth affine group scheme whose fibres
have reductive identity components, the set of points with connected fibre is closed.

## Statement and quantifiers

The proposition quantifies over:

- a scheme `S : Scheme.{u}`;
- a group scheme `G : GroupScheme S` with the instances `Smooth G.X.hom` and
  `IsAffineHom G.X.hom`. This is Conrad's smooth `S`-affine group `G → S`;
- a proof of `identityComponentReductiveLocus G = Set.univ`. Here
  `identityComponentReductiveLocus G` is the set of points `s` of `S` such that the
  identity component of the geometric fibre `G_{s̄}` is connected reductive
  (`IsConnectedReductive`). This is Conrad's hypothesis "each `G⁰_s` is reductive"; see
  the derivation below.

It then introduces the local abbreviation `ConnectedFibre s`, for `s : S`: the
underlying topological space of the scheme `(RelativeIdentityComponent.residueFiber G s).X.left`
is connected (`ConnectedSpace`). This scheme is the pullback of `G.X.hom` along the
canonical morphism `Spec κ(s) ⟶ S`, that is, Conrad's fibre `G_s` over the residue field
`k(s)`. A group scheme has an identity section, so this fibre is nonempty.

## Conclusion

The conclusion is the conjunction of two assertions.

1. The set `{s : S | ConnectedFibre s}` is closed in `S`.
2. For every point `η : S` with `IsGenericPoint η Set.univ`, if `ConnectedFibre η` holds
   then `ConnectedFibre s` holds for every `s : S`. In Mathlib,
   `IsGenericPoint η Set.univ` means that the closure of `{η}` is all of `S`. Such a point
   exists exactly when `S` is irreducible, since the closure of a point is irreducible
   and every irreducible closed subset of a scheme has a generic point.

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I, Panoramas
et Synthèses 42–43, SMF, 2014. It is registered as `conrad-2014-reductive-group-schemes`,
file `Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers are
the printed page numbers.

- Proposition 3.1.12, p.89: "Let G → S be a smooth S-affine group such that each G⁰_s
  is reductive. The locus of s ∈ S such that G_s is connected is closed in S. In
  particular, if S is irreducible and the generic fiber is connected then all fibers
  are connected." The proof is on pp.89–90.
- In the proof, p.89: "Since G_s is connected if and only if it is geometrically
  connected over k(s), the set Y of points s ∈ S such that G_s is connected is
  constructible [EGA, IV₃, 9.7.7(ii)]."
- After the proof, p.90: "note that the locus of connected fibers can fail to be open
  (Example 3.1.4)."
- Definition 3.1.1, p.81: "A reductive S-group is a smooth S-affine group scheme G → S
  such that the geometric fibers G_s̄ are connected reductive groups."

## Derivation from the source

- **Hypothesis.** `G⁰_s` is the identity component of the fibre `G_s` over `k(s)`. A
  smooth connected affine group over a field is reductive when its geometric fibre is
  connected reductive (Definition 3.1.1 and the remark after it). The identity
  component commutes with extension of the ground field for groups locally of finite
  type, so "each `G⁰_s` is reductive" says that for every `s` the identity component of
  the geometric fibre `G_{s̄}` is connected reductive. That is
  `identityComponentReductiveLocus G = Set.univ`.
- **Connected fibres.** Conrad's "`G_s` is connected" refers to the fibre over the
  residue field `k(s)`, and connectedness of a scheme is connectedness of its
  underlying topological space. The proposition encodes it with the residue-field fibre
  of [`RelativeIdentityComponent`](../RelativeIdentityComponent.md), not with the
  geometric fibre. By the remark in Conrad's proof the two conditions agree for group
  schemes; the proposition does not state this.
- **Second assertion.** Conrad's "if `S` is irreducible and the generic fibre is
  connected" is encoded by a point `η` whose closure is `S` together with
  `ConnectedFibre η`. The existence of `η` forces `S` to be irreducible, and in an
  irreducible scheme the generic point is unique, so no separate irreducibility
  hypothesis is needed. The second assertion follows from the first, since a closed set
  containing `η` contains its closure; it is stated because Conrad states it.

## Scope

All objects are in universe `u`. The proposition does not state:

- the constructibility of the connected-fibre locus, or the agreement of connectedness
  and geometric connectedness of the fibres, both used in Conrad's proof;
- the failure of openness of the locus (Example 3.1.4);
- Proposition 3.1.3, from which Conrad notes that Proposition 3.1.12 also follows (that
  `G⁰` is an open subgroup with `G/G⁰` a finitely presented separated étale `S`-group).

## Relation to the Library

- `IdentityComponentReductiveLocusOpenStatement` in
  [`Reductive.IdentityComponentLocus`](IdentityComponentLocus.md) is Conrad's
  Proposition 3.1.9(1): the locus where the identity component of the geometric fibre is
  reductive is open. The present proposition assumes that this locus is everything.

This module proves none of these relations.
