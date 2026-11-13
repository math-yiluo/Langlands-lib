# Statement: dynamic subgroups over any base scheme are smooth with connected fibres

Worker 3483.

`Langlands.GroupScheme.DynamicBaseSmoothConnectedStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it
adds no other definitions, theorems or axioms. It imports
[`Dynamic.Basic`](Basic.md) (for `Dynamic.parabolic`, `Dynamic.centralizer`,
`Dynamic.unipotent` and `SubgroupFunctor.IsRepresentedBy`) and Mathlib's
`Mathlib.AlgebraicGeometry.Geometrically.Connected` (for
`GeometricallyConnected`).

It is the version over an arbitrary base scheme of
[`DynamicRingSmoothConnectedStatement`](RingSmoothConnectedStatement.md), which states
the same three implications over an affine base `Spec R`. The only change is the base:
`S : Scheme.{u}` in place of `Spec (CommRingCat.of R)`.

## Statement and quantifiers

The proposition quantifies over:

- every scheme `S : Scheme.{u}`, not necessarily affine;
- every group scheme `G : GroupScheme S` whose structure morphism `G.X.hom` is `Smooth`
  and `IsAffineHom` (instance arguments);
- every cocharacter `χ : (Gm S).toGrp ⟶ G`;
- every group scheme `H` over `S` and every homomorphism `j : H ⟶ G`.

It asserts the conjunction of three implications:

1. if `(Dynamic.unipotent χ).IsRepresentedBy j`, then `Smooth H.X.hom` and
   `GeometricallyConnected H.X.hom`;
2. if `(Dynamic.parabolic χ).IsRepresentedBy j`, then `Smooth H.X.hom`, and
   `GeometricallyConnected G.X.hom → GeometricallyConnected H.X.hom`;
3. if `(Dynamic.centralizer χ).IsRepresentedBy j`, then `Smooth H.X.hom`, and
   `GeometricallyConnected G.X.hom → GeometricallyConnected H.X.hom`.

- `Dynamic.parabolic χ`, `Dynamic.unipotent χ` and `Dynamic.centralizer χ` are the
  subgroup functors of points `g` of `G` for which the orbit map `t ↦ χ(t) g χ(t)⁻¹`
  extends to the affine line, extends with value `1` at `0`, or is constant
  ([`Dynamic.Basic`](Basic.md)). They are defined over any base scheme.
- `F.IsRepresentedBy j` says that `j` is a monomorphism of the underlying schemes over
  `S` and that its range subgroup functor is `F`
  ([`SubgroupFunctor`](../SubgroupFunctor.md)). Nothing asserts that such an `H`
  exists, and the representative is arbitrary.
- `IsAffineHom G.X.hom` says that the structure morphism `G → S` is affine: the preimage
  of every affine open of `S` is affine. `G` itself need not be an affine scheme.
- `GeometricallyConnected f` (Mathlib) says that for every field `K : Type u` and every
  morphism `Spec K ⟶ S`, the pullback of `f` along it is a connected space. For
  `H.X.hom` this says that every fibre of `H` over a point of `S` is geometrically
  connected.

The trivial cocharacter is included.

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I,
Panoramas et Synthèses 42–43, SMF, 2014; registered as
`conrad-2014-reductive-group-schemes`, file
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers are
one-based PDF pages, which agree with the printed page numbers of this file.

Theorem 4.1.7 (pp.112–113) is stated for "a finitely presented affine group over a
ring k" with an action `λ : G_m × G → G`:

- part 1 (p.112): the functors "are represented by respective finitely presented
  closed subgroups `P_G(λ)`, `U_G(λ)`, and `Z_G(λ)` of `G`";
- part 2 (p.113): "The fibers of `U_G(λ) → S` are connected, and so are the fibers of
  `P_G(λ)` and `Z_G(λ)` if `G → S` has connected fibers.";
- part 4, first sentence (p.113): "Assume `G` is smooth. The subgroups `P_G(λ)`,
  `U_G(λ)`, and `Z_G(λ)` are smooth".

Right after the theorem (p.113): "When we apply Theorem 4.1.7 to examples in which the
action arises from conjugation against a 1-parameter subgroup λ : G_m → G, we shall
denote the resulting closed subgroups as `P_G(λ)`, `U_G(λ)`, and `Z_G(λ)`."

After Example 4.1.9 (p.114): "It is immediate from the definitions that the formation of
`P_G(λ)`, `U_G(λ)`, and `Z_G(λ)` commutes with any base change on k, and that Theorem
4.1.7 adapts to work over any base scheme S (not just affine schemes)."

James S. Milne, *Algebraic Groups* (2017), registered as `milne-2017-algebraic-groups`
(SHA-256 `899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`), Summary
1.36 (printed p.17, PDF p.33): "The following conditions on an algebraic group G over k
are equivalent: (a) G is irreducible; (b) G is connected; (c) G is geometrically
connected."

## Derivation from the source

The Lean proposition is the case of Theorem 4.1.7(2) and of the smoothness assertion of
4.1.7(4), in the version over an arbitrary base scheme `S` that Conrad states after
Example 4.1.9, in which the action is conjugation through a cocharacter and `G` is
smooth.

- Base and action. `S` is any scheme, as in Conrad's remark on p.114. The `G_m`-action
  is conjugation through `χ`, which is the case Conrad writes `P_G(λ)`, `U_G(λ)`,
  `Z_G(λ)`. The Library's dynamic subgroups are defined only for this action.
- Finite presentation. Over a general base, the hypothesis "finitely presented affine
  group" of Theorem 4.1.7 reads: `G → S` is affine and of finite presentation. A smooth
  morphism is locally of finite presentation, and an affine morphism is quasi-compact
  and quasi-separated, so a `G` with smooth affine structure morphism satisfies it.
- Smoothness. Clauses 1–3 conclude that `H` is smooth over `S`, which is part 4's first
  sentence. `H` is isomorphic to Conrad's representing subgroup because both represent
  the same subgroup functor through monomorphisms.
- Connectedness. Conrad says "connected"; the Lean statement says geometrically
  connected, both for `H` and in the hypothesis on `G`. Every fibre of `G`, `P_G(λ)`,
  `U_G(λ)` or `Z_G(λ)` over a point `s` of `S` is an algebraic group over the residue
  field `κ(s)` (finitely presented by part 1), so Milne's Summary 1.36 makes "connected"
  and "geometrically connected" equivalent for each of these fibres. Hence clause 1 and
  the connectedness halves of clauses 2–3 are equivalent to part 2.

So the proposition is no stronger than Conrad's theorem over a base scheme.

## Scope

All objects are in universe `u`; the field tests in `GeometricallyConnected` are in
`Type u`. The base `S` is arbitrary: it need not be affine, Noetherian, quasi-compact or
connected. Not stated here: the representability of part 1 over a non-affine base (the
statement assumes a representative `j` and does not assert that one exists); Theorem
4.1.7 for abstract `G_m`-actions or for non-smooth `G` (part 2 holds for finitely
presented `G`); the decomposition of part 3; and the open cell, Lie algebra and
unipotence assertions of part 4.

## Relation to the Library

- [`DynamicRingSmoothConnectedStatement`](RingSmoothConnectedStatement.md) is the case
  `S = Spec R` of an affine base.
- `DynamicSmoothStatement` and `DynamicConnectedStatement`
  ([`SmoothConnectedStatement`](SmoothConnectedStatement.md)) are the case of a base
  field. Their connectedness conclusion is `ConnectedSpace` of the scheme over the
  field, and their hypothesis on `G` is `ConnectedSpace G.X.left`.
- The published theorem `dynamicSmooth_ring` ([`SmoothOverRing`](SmoothOverRing.md))
  has the smoothness halves of the three clauses over an affine base `Spec R` as its
  conclusion.
- The family 8 ledger (`notes/group-schemes/ledger-family-8-relative.md`, row F1)
  records the smoothness of the dynamic subgroups over a non-affine base as having no
  Lean statement.

This module proves none of these relations.
