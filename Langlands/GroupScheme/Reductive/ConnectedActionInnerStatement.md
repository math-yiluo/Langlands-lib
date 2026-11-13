# Statement: actions of groups with connected fibres on reductive groups are inner

Worker 75.

`Langlands.GroupScheme.ReductiveConnectedActionInnerStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It imports:

- [`AutomorphicAction`](../AutomorphicAction.md), for `AutomorphicAction`,
  `AutomorphicAction.restrict` and `AutomorphicAction.conjugation`;
- [`Reductive.Basic`](Basic.md), for `IsReductive`; the base-change functor
  `GroupScheme.baseChange` of [`AbelianScheme.GroupScheme`](../../AbelianScheme/GroupScheme.md)
  comes transitively;
- [`Rational.Characters`](../Rational/Characters.md), for the centre `center G`;
- [`Rational.RootSubgroupStructureStatement`](../Rational/RootSubgroupStructureStatement.md),
  for `RelativeRoot.IsFppfQuotient`.

`GroupScheme S` is `Grp (Over S)`, and a morphism `H ⟶ G` in it is a homomorphism of
group schemes over `S`.

## Predicates and constructions used

- `IsReductive G`: the structure morphism of `G` is smooth and affine, and every geometric
  fibre of `G` is a (connected) reductive group over an algebraically closed field.
- `(GroupScheme.baseChange (S.fromSpecResidueField s)).obj H` is the fibre `H_s` of `H`
  over the residue field `κ(s)` of the point `s`: the pullback of `H` along
  `Spec κ(s) ⟶ S`, with its induced group law. `.X.left` is its underlying scheme.
- `center G`: the subgroup functor of `G` whose points over `T` are the `g : T ⟶ G.X`
  such that for every `T' ⟶ T` the restriction of `g` commutes with every point of `G`
  over `T'`. This is the functor of points of the scheme-theoretic centre `Z_G`.
- `RelativeRoot.IsFppfQuotient N q`: the underlying morphism of `q` is flat, surjective
  and locally of finite presentation, and the range of the scheme kernel of `q` is `N`.
- `AutomorphicAction H G`: a morphism `hom : H.X ⊗ G.X ⟶ G.X` over `S` that is an action
  of `H` on `G` by group automorphisms, with the identity, composition and
  multiplicativity laws required on the points over every `T : Over S`.
- `a.restrict f`, for `f : K ⟶ H`, is the action of `K` on `G` through `f`: on points,
  `k` acts as `f(k)`.
- `AutomorphicAction.conjugation (𝟙 G)` is the conjugation action of `G` on itself,
  `g · x = g x g⁻¹` on points.

## Statement and quantifiers

The proposition quantifies over every scheme `S : Scheme.{u}`, every
`G H : GroupScheme S` such that

- `IsReductive G`, and
- for every point `s : S`, the underlying scheme of the fibre `H_s` is a connected
  topological space;

then over every `Gad : GroupScheme S` and `p : G ⟶ Gad` with
`RelativeRoot.IsFppfQuotient (center G) p`, and every `c : AutomorphicAction Gad G` with
`c.restrict p = AutomorphicAction.conjugation (𝟙 G)`. It asserts:

for every `a : AutomorphicAction H G` there is a unique homomorphism `φ : H ⟶ Gad` with
`c.restrict φ = a`.

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I,
Panoramas et Synthèses 42–43, SMF, 2014. It is registered as
`conrad-2014-reductive-group-schemes`, file
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers are
the one-based PDF pages, which agree with the printed page numbers.

- Proposition 7.2.6, p.253: "Let G → S be a reductive group scheme, and H → S a group
  scheme with connected fibers. Any action of H on G must be through inner
  automorphisms; i.e., it is the composition of a unique S-homomorphism H → G/Z_G
  followed by the natural action of G/Z_G on G."
- Proof of Proposition 7.2.6, p.253: "To give an action of H on G is to give an
  S-homomorphism H → Aut_{G/S}, so we just have to show that the composite map
  H → Out_{G/S} is trivial. Since Out_{G/S} is locally constant over S, it suffices to
  work on geometric fibers over S, where the result is clear since each fiber H_s is
  connected."
- Theorem 7.1.9(1), p.245: for a reductive group `G` over a non-empty scheme `S`, the
  functor `Aut_{G/S}` is represented by a separated smooth `S`-group `Aut_{G/S}` that
  fits into a short exact sequence `1 → G/Z_G → Aut_{G/S} → Out_{G/S} → 1`, where
  "G/Z_G is closed in Aut_{G/S}, Out_{G/S} is a separated étale S-group that is locally
  constant for the étale topology on S".
- p.253, before Proposition 7.2.6: "An automorphism φ ∈ Aut_{G/S}(S′) is inner if it
  arises from (G/Z_G)(S′)".

## Derivation from the source

- **Actions.** Conrad's "action of H on G" is an action by group automorphisms, which he
  identifies with an `S`-homomorphism `H → Aut_{G/S}`. It is encoded by the Library's
  `AutomorphicAction H G`: one morphism of schemes `H × G → G` with the action laws on all
  test points. No automorphism scheme is needed to state the result, because the
  proposition is about actions, and `Aut_{G/S}` appears only in the proof.
- **`G/Z_G`.** The adjoint quotient is a group scheme `Gad` with a homomorphism
  `p : G ⟶ Gad` that is flat, surjective and locally of finite presentation with kernel
  `center G`, that is, an fppf quotient of `G` by `Z_G`. Any such `p` identifies `Gad`
  with the fppf quotient sheaf `G/Z_G`.
- **The natural action of `G/Z_G`.** Conrad's "natural action of G/Z_G on G" is the
  action induced by conjugation of `G` on itself, which is trivial on `Z_G`. It is
  encoded as an action `c` of `Gad` on `G` whose restriction along `p` is conjugation.
  Since `p` is faithfully flat and locally of finite presentation, so is its base change
  `p × 𝟙 : G × G → Gad × G`, which is therefore an epimorphism of schemes. Hence at most one
  action `c` satisfies this condition, and `c` is the natural action.
- **"The composition of a unique S-homomorphism H → G/Z_G followed by the natural
  action".** The composite of `φ : H ⟶ Gad` with the natural action is `c.restrict φ`.
  The conclusion asserts that exactly one `φ` gives `a`.
- **Connected fibres.** Conrad's fibres `H_s` are the fibres over the points `s ∈ S`, here
  the base change of `H` to `Spec κ(s)`; "connected" is connectedness of its underlying
  topological space. No finiteness, flatness, smoothness or affineness hypothesis on `H`
  is made, as in the source. The source's proof reduces to geometric fibres; a connected
  scheme over a field with a rational point (here the identity) is geometrically
  connected, so the residue-fibre condition implies the geometric one. The proposition
  also holds directly with the residue-fibre condition: `Out_{G/S}` is étale and
  separated, so its identity section is open and closed. Its preimage under
  `H → Out_{G/S}` is open and closed in `H`, and it meets each connected fibre `H_s` in
  the identity, so it is all of `H`.

## Scope

All objects are in universe `u`. The base `S` is an arbitrary scheme: it need not be
affine, Noetherian, reduced or connected. The empty scheme is allowed, and over it the
statement holds trivially. The group scheme `H` is arbitrary apart from the
connected-fibre condition. No splitting of `G` and no maximal torus of `G` is assumed.

## Not stated

The statement does not assert that the quotient `G/Z_G` or the action `c` exist. Their
existence is part of the theory of reductive group schemes (Conrad §3.3, Theorem 7.1.9),
not of this proposition; without such `Gad`, `p` and `c` the statement holds vacuously.
It does not state the representability of `Aut_{G/S}`, the exact sequence of
Theorem 7.1.9, or the converse that every homomorphism `H ⟶ Gad` gives an action (this
is `c.restrict φ`, a construction).
