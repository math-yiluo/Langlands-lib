# Statement: the semisimple identity-component locus is open

Worker 75.

`Langlands.GroupScheme.IdentityComponentSemisimpleLocusOpenStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It imports
[`Reductive.IdentityComponentLocus`](IdentityComponentLocus.md) and
[`Reductive.Semisimple`](Semisimple.md). Through these imports it uses:

- `geometricPoint` and `geometricFiber` from [`Reductive.Basic`](Basic.md). For a
  point `s : S`, `geometricPoint S s` is the canonical morphism
  `Spec (AlgebraicClosure κ(s)) ⟶ S`, and `geometricFiber G s` is the group scheme
  over `Spec (AlgebraicClosure κ(s))` whose structure morphism is
  `pullback.snd G.X.hom (geometricPoint S s)`;
- `identityComponent` from [`IdentityComponent`](../IdentityComponent.md): the open and
  closed identity-component subgroup scheme of a smooth affine group scheme over a
  field;
- `IsSemisimple` from [`Reductive.Semisimple`](Semisimple.md): a group scheme over a
  field is semisimple when it is connected reductive (`IsConnectedReductive`) and its
  full scheme-theoretic centre is represented by a finite closed subgroup
  (`HasFiniteCenter`);
- `GroupScheme` from `Langlands.AbelianScheme.GroupScheme`; `GroupScheme S` is
  `Grp (Over S)`.

It states the semisimplicity assertion in Conrad's Proposition 3.1.9(1): for a smooth
affine group scheme, the set of points at which the identity component of the fibre is
semisimple is open.

## Statement and quantifiers

The proposition quantifies over:

- a scheme `S : Scheme.{u}`;
- a group scheme `G : GroupScheme S` with the instances `Smooth G.X.hom` and
  `IsAffineHom G.X.hom`. This is Conrad's smooth `S`-affine group `G → S`. No
  connectedness of the fibres and no Noetherian or irreducibility hypothesis on `S` is
  assumed.

It asserts that the set

`{s : S | IsSemisimple (identityComponent (geometricFiber G s))}`

is open in `S`.

Inside the set-builder, two `haveI` lines supply the instances
`Smooth (geometricFiber G s).X.hom` and `IsAffineHom (geometricFiber G s).X.hom`, which
`identityComponent` requires. Both are obtained by `inferInstanceAs` from the
corresponding instances of `pullback.snd G.X.hom (geometricPoint S s)`, that is, from
stability of smoothness and affineness under base change. This is the same device as the
local instances `geometricFiber_smooth` and `geometricFiber_isAffineHom` in
[`Reductive.IdentityComponentLocus`](IdentityComponentLocus.md). Both instances are
propositions, so the statement does not depend on how they are proved.

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I, Panoramas
et Synthèses 42–43, SMF, 2014. It is registered as `conrad-2014-reductive-group-schemes`,
file `Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers are
the printed page numbers.

- Proposition 3.1.9, p.85: "Let G → S be a smooth S-affine group scheme and suppose
  G⁰_s is reductive for some s ∈ S. 1. There is an open U around s in S such that G⁰_u
  is reductive for all u ∈ U. The same holds for semisimplicity." The proof of part (1)
  is on pp.86–88.
- In the proof, p.88: "It remains to check that when G⁰ → S has reductive geometric
  fibers, semisimplicity of a geometric fiber G⁰_s̄ implies semisimplicity of geometric
  fibers at points near s." Conrad then reads semisimplicity of a connected reductive
  group `H` over an algebraically closed field off its root system `Ψ`, as
  `dim H = #Ψ + rank(Ψ)`.
- Definition 3.1.1, p.81: "A reductive S-group is a smooth S-affine group scheme G → S
  such that the geometric fibers G_s̄ are connected reductive groups. A semisimple
  S-group is a reductive S-group whose geometric fibers are semisimple." The remark
  that follows (p.81) says that it suffices to check reductivity, resp. semisimplicity,
  at a single geometric point over each `s`.

## Derivation from the source

- **Fibres.** `G⁰_u` is the identity component of the fibre `G_u` over the residue field
  `k(u)`. By Definition 3.1.1 applied over `Spec k(u)`, `G⁰_u` is semisimple when its
  geometric fibre is a semisimple connected reductive group. For a group scheme locally
  of finite type over a field, the identity component commutes with extension of the
  ground field, so the geometric fibre of `G⁰_u` is the identity component of the
  geometric fibre `G_ū`. The statement therefore uses
  `identityComponent (geometricFiber G u)`, with one chosen algebraic closure of each
  residue field. By the remark after Definition 3.1.1, the choice of geometric point
  does not matter.
- **Semisimplicity.** Conrad calls a connected reductive group over an algebraically
  closed field semisimple when its radical is trivial. The Library predicate
  `IsSemisimple` instead requires connected reductivity together with a finite
  scheme-theoretic centre. For connected reductive groups the two conditions agree:
  this is Milne, *Algebraic Groups* (2017), Proposition 19.10, the source of the
  Library definition (see [`Reductive.Semisimple`](Semisimple.md)). The Library does
  not prove this equivalence, and the present proposition does not state it.
- **Openness.** Conrad's "the same holds for semisimplicity" says: if `G⁰_s` is
  semisimple, then there is an open `U` around `s` such that `G⁰_u` is semisimple for
  all `u ∈ U`. This holds for every `s` exactly when the set of such points is open,
  which is the stated `IsOpen`. Semisimplicity of `G⁰_s` includes its reductivity, so
  Conrad's standing hypothesis that `G⁰_s` is reductive is automatic here.

## Scope

All objects are in universe `u`. The proposition does not state:

- the reductivity assertion of Proposition 3.1.9(1); that is
  `IdentityComponentReductiveLocusOpenStatement` (see below);
- Proposition 3.1.9(2), on spreading out maximal tori;
- the equivalence between finiteness of the centre and triviality of the radical for
  connected reductive groups, or any comparison with the residue-field fibres `G_u`.

## Relation to the Library

- `IdentityComponentReductiveLocusOpenStatement` in
  [`Reductive.IdentityComponentLocus`](IdentityComponentLocus.md) is the reductivity
  assertion of Conrad's Proposition 3.1.9(1): the set
  `identityComponentReductiveLocus G` of points `s` at which
  `identityComponent (geometricFiber G s)` is connected reductive is open. The set in
  the present proposition is contained in that locus, because `IsSemisimple` includes
  `IsConnectedReductive`. The present proposition is stated with the same geometric
  fibres, the same identity components and the same instance device.

This module proves none of these relations.
