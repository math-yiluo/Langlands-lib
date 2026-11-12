# Statement: dynamic subgroups over a ring are smooth with connected fibres

Worker 3483.

`Langlands.GroupScheme.DynamicRingSmoothConnectedStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it
adds no other definitions, theorems or axioms. It imports
[`Dynamic.Basic`](Basic.md) (for `Dynamic.parabolic`, `Dynamic.centralizer`,
`Dynamic.unipotent` and `SubgroupFunctor.IsRepresentedBy`) and Mathlib's
`Mathlib.AlgebraicGeometry.Geometrically.Connected` (for
`GeometricallyConnected`).

## Statement and quantifiers

The proposition quantifies over:

- every commutative ring `R : Type u`;
- every group scheme `G : GroupScheme (Spec (CommRingCat.of R))` whose structure
  morphism `G.X.hom` is `Smooth` and `IsAffineHom` (instance arguments);
- every cocharacter `χ : (Gm (Spec (CommRingCat.of R))).toGrp ⟶ G`;
- every group scheme `H` over `Spec R` and every homomorphism `j : H ⟶ G`.

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
  ([`Dynamic.Basic`](Basic.md)).
- `F.IsRepresentedBy j` says that `j` is a monomorphism of the underlying schemes over
  `Spec R` and that its range subgroup functor is `F`
  ([`SubgroupFunctor`](../SubgroupFunctor.md)). Nothing asserts that such an `H`
  exists, and the representative is arbitrary.
- `GeometricallyConnected f` (Mathlib) says that for every field `K : Type u` and every
  morphism `Spec K ⟶ Spec R`, the pullback of `f` along it is a connected space. For
  `H.X.hom` this says that every fibre of `H` over a point of `Spec R` is geometrically
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
denote the resulting closed subgroups as `P_G(λ)`, `U_G(λ)`, and `Z_G(λ)`." After
Example 4.1.9 (p.114): "Theorem 4.1.7 adapts to work over any base scheme S (not just
affine schemes)".

James S. Milne, *Algebraic Groups* (2017), registered as `milne-2017-algebraic-groups`
(SHA-256 `899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`), Summary
1.36 (printed p.17, PDF p.33): "The following conditions on an algebraic group G over k
are equivalent: (a) G is irreducible; (b) G is connected; (c) G is geometrically
connected."

## Derivation from the source

The Lean proposition is the case of Theorem 4.1.7(2) and of the smoothness assertion of
4.1.7(4) in which the base is affine, the action is conjugation through a cocharacter,
and `G` is smooth.

- Base and action. `S = Spec R`, and the `G_m`-action is conjugation through `χ`, which
  is the case Conrad writes `P_G(λ)`, `U_G(λ)`, `Z_G(λ)`. The Library's dynamic
  subgroups are defined only for this action.
- Finite presentation. `G` smooth and affine over the affine base `Spec R` is finitely
  presented over `R`, so Conrad's hypothesis holds.
- Smoothness. Clauses 1–3 conclude that `H` is smooth, which is part 4's first
  sentence; `H` is isomorphic to Conrad's representing subgroup because both represent
  the same subgroup functor through monomorphisms.
- Connectedness. Conrad says "connected"; the Lean statement says geometrically
  connected, both for `H` and in the hypothesis on `G`. Every fibre of `G`, `P_G(λ)`,
  `U_G(λ)` or `Z_G(λ)` over a point `s` is an algebraic group over the residue field
  `κ(s)` (finitely presented by part 1), so Milne's Summary 1.36 makes "connected" and
  "geometrically connected" equivalent for each of these fibres. Hence clause 1 and the
  connectedness halves of clauses 2–3 are equivalent to part 2.

So the proposition is no stronger than Conrad's theorem.

## Scope

All objects are in universe `u`; the field tests in `GeometricallyConnected` are in
`Type u`. The ring `R` is arbitrary: it need not be Noetherian, local or a domain. Not
stated here: Theorem 4.1.7 over a non-affine base, for abstract `G_m`-actions, or for
non-smooth `G` (part 2 holds for finitely presented `G`); the decomposition of part 3;
and the open cell, Lie algebra and unipotence assertions of part 4.

## Relation to the Library

- `DynamicSmoothStatement` and `DynamicConnectedStatement`
  ([`SmoothConnectedStatement`](SmoothConnectedStatement.md)) are the case of a base
  field. Their connectedness conclusion is `ConnectedSpace` of the scheme over the
  field, and their hypothesis on `G` is `ConnectedSpace G.X.left`.
- The published theorem `dynamicSmooth_ring` ([`SmoothOverRing`](SmoothOverRing.md))
  has the smoothness halves of the three clauses as its conclusion. It is a theorem
  with explicit arguments, not a named proposition.
- The family 8 ledger (`notes/group-schemes/ledger-family-8-relative.md`, row F1)
  records the connectedness of fibres over a ring as having no Lean statement.

This module proves none of these relations.
