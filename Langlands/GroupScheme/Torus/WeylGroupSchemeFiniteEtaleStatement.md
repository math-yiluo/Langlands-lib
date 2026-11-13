# Statement: the Weyl group scheme of a maximal torus is finite étale

Worker 75.

`Langlands.GroupScheme.WeylGroupSchemeFiniteEtaleStatement.{u} : Prop` is a statement-only,
`Prop`-valued definition. This module does not prove it, and it adds no other definitions,
theorems or axioms. It imports:

- [`Rational.TorusNormalizer`](../Rational/TorusNormalizer.md), for `torusNormalizer` and,
  through its imports, `torusCentralizer`, `SubgroupFunctor.IsRepresentedBy` and
  `IsClosedSubgroup`;
- [`Torus.FieldPointMaximality`](FieldPointMaximality.md), for `IsFibrewiseMaximalTorus`;
- [`Torus.Relative`](Relative.md), for `RelativeTorus.IsTorus`;
- [`Reductive.Basic`](../Reductive/Basic.md), for `IsReductive`.

## Statement and quantifiers

The proposition quantifies over every scheme `S : Scheme.{u}`, every group scheme
`G : GroupScheme S` with `IsReductive G`, every commutative group scheme
`T : CommGroupScheme S` and every homomorphism `t : T.toGrp ⟶ G`. `IsReductive G` says that
`G` is smooth and affine over `S` and that every geometric fibre is a connected reductive
group. The torus hypotheses are:

1. `RelativeTorus.IsTorus T.toGrp`: `T` becomes a split torus on some étale cover of `S`;
2. `IsClosedSubgroup t`: the underlying morphism of schemes of `t` is a closed immersion;
3. `IsFibrewiseMaximalTorus t`: for every point `s` of `S`, the pullback of `t` to the
   residue field `κ(s)` satisfies `IsMaximalTorus`. In that fibre the torus is a closed
   subgroup and factors through no strictly larger closed `κ(s)`-torus of the fibre of `G`.

The conclusion asserts that there exist group schemes `N`, `Z`, `W` over `S` and
homomorphisms `n : N ⟶ G`, `z : Z ⟶ G`, `q : N ⟶ W` with the following properties.

- `IsClosedSubgroup n` and `(torusNormalizer t).IsRepresentedBy n`. The second condition
  says that `n` is a monomorphism and that the points of `G` factoring through `n` are
  exactly the points of the normalizer subgroup functor. A point `g` of `G` over an
  `S`-scheme `U` lies in `torusNormalizer t` when, after every refinement `V ⟶ U`,
  conjugation by `g` and by `g⁻¹` sends every point of `G` that factors through `t` to such
  a point. So `n` is a closed subgroup representing `N_G(T)`.
- `IsClosedSubgroup z` and `(torusCentralizer t).IsRepresentedBy z`. A point `g` over `U`
  lies in `torusCentralizer t` when, after every refinement `V ⟶ U`, it commutes with every
  point of `T` pushed into `G`. So `z` is a closed subgroup representing `Z_G(T)`.
- `IsFinite W.X.hom` and `Etale W.X.hom`: the structure morphism of `W` is finite and
  étale.
- The underlying morphism of schemes `q.hom.hom.left` of `q` is flat, surjective and
  locally of finite presentation. So it is an fppf covering.
- For every `S`-scheme `U` and every point `y : U ⟶ N.X`, `y ≫ q.hom.hom = 1` holds if and
  only if `y ≫ n.hom.hom` lies in `torusCentralizer t` over `U`. So the kernel of `q` is
  `Z_G(T)`, viewed inside `N`.

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I, Panoramas
et Synthèses 42–43, SMF, 2014. It is registered as `conrad-2014-reductive-group-schemes`,
file `Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers are
printed page numbers, which agree with the one-based PDF page numbers of this file.

- Proposition 3.2.8, p.96: "Let T be a maximal torus in a reductive group scheme G → S.
  The Weyl group W_G(T) := N_G(T)/Z_G(T) is finite étale over S." The remark that follows
  recalls Theorem 2.3.1 for the quotient sheaf.
- Theorem 2.3.1, p.67: for a smooth `S`-affine group `G` and a subgroup `H` of
  multiplicative type, the quotient `W_G(H) := N_G(H)/Z_G(H)` exists as a separated étale
  `S`-group of finite presentation.
- Proposition 2.1.2, p.56: for a multiplicative type subgroup `Y` of a finitely presented
  `S`-affine group `G`, the normalizer `N_G(Y)` exists as a finitely presented closed
  subgroup of `G`; it is smooth when `G` is smooth.
- Lemma 2.2.4, pp.64–65: in the same situation the centralizer `Z_G(Y)` exists as a
  finitely presented closed subgroup; it is smooth when `G` is smooth.
- Definition 3.2.1, p.91 (maximal tori via geometric fibres); Remark A.1.2, p.267
  (geometric maximality agrees with maximality among tori over a field); Proposition B.3.4,
  pp.290–291 (groups of multiplicative type are étale-locally diagonalizable); Lemma B.1.3,
  p.281 (a monic homomorphism from a group of multiplicative type to an affine finitely
  presented group is a closed immersion).

## Derivation from the source

The statement is derived from Proposition 3.2.8; it is not a quotation.

**Maximal torus.** Hypotheses 1–3 encode "maximal torus of `G`" in the same way as the
Library's other relative maximal-torus statements. An `S`-torus is étale-locally split by
Proposition B.3.4. Requiring a closed immersion adds nothing by Lemma B.1.3. Maximality on
residue fibres agrees with geometric maximality fibre by fibre by Remark A.1.2.

**Normalizer and centralizer.** Conrad's `N_G(T)` is the functor of points `g` with
`g T g⁻¹ = T` after base change, and `Z_G(T)` is the functor of points that centralize `T`
after base change. The Library's `torusNormalizer t` and `torusCentralizer t` are these
functors, tested after every refinement of the test scheme. Proposition 2.1.2 and
Lemma 2.2.4 represent them by closed subgroups. The proposition asserts these
representatives as part of its conclusion, because the Library has no general-base
representability theorem for them.

**The quotient.** The fppf quotient sheaf `N/Z` is represented by a scheme `W` exactly when
there is a homomorphism `q : N ⟶ W` that is an fppf covering with kernel `Z`.

- If `q` is such a map, then the induced map of sheaves `N/Z → W` is injective because the
  kernel is `Z`. It is surjective because every point of `W` lifts to `N` after the fppf
  base change along `q`.
- Conversely, take `W = N/Z` from Theorem 2.3.1 and `q` the quotient map. The kernel of
  `q` is `Z`. Since `Z` is smooth by Lemma 2.2.4, `q` is a `Z`-torsor over `W`, so `q` is
  smooth and surjective. In particular `q` is flat and locally of finite presentation.

Proposition 3.2.8 adds that `W` is finite étale, which is `IsFinite W.X.hom` and
`Etale W.X.hom`.

## Scope

All objects are in universe `u`, and the base `S` is an arbitrary scheme. The proposition
does not assert that `N` or `Z` is smooth, that `Z_G(T) = T`, or that the formation of `W`
commutes with base change. It also does not identify the geometric fibres of `W` with the
Weyl groups of the root systems of the fibres, and it does not state the more general
Theorem 2.3.1 for smooth affine groups and multiplicative type subgroups.

## Relation to the Library

- [`Torus.NormalizerSmoothStatement`](NormalizerSmoothStatement.md) states, over a field,
  that the normalizer of a closed torus in a smooth affine group has a smooth closed
  representative.
- [`Rational.TorusNormalizer`](../Rational/TorusNormalizer.md) defines the normalizer
  functor used here. Over every test scheme `U` it forms the point quotient group
  `N(U)/Z(U)` and the restriction map to it from the published `relativeWeylGroup`.

This module proves none of these relations.
