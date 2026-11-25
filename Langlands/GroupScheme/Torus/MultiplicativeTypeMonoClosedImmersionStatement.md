# Statement: monic homomorphisms from groups of multiplicative type are closed immersions

`Langlands.GroupScheme.MultiplicativeTypeMonoClosedImmersionStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It imports:

- [`Torus.RelativeMultiplicativeType`](RelativeMultiplicativeType.md), for the relative
  predicate `RelativeMultiplicativeType.IsMultiplicativeType` (Conrad, Definition B.1.1);
- [`Reductive.Basic`](../Reductive/Basic.md), for `IsClosedSubgroup`.

`GroupScheme S` is `Grp (Over S)`, and a morphism `j : H ⟶ G` in it is a homomorphism of
group schemes over `S`. Its underlying morphism of `S`-schemes is `j.hom.hom : H.X ⟶ G.X`.

## Predicates used

- `RelativeMultiplicativeType.IsMultiplicativeType H`: there is an fppf cover of `S` (a
  jointly surjective family of flat morphisms `S_i ⟶ S` locally of finite presentation)
  such that each base change `H_{S_i}` is isomorphic, as a group scheme over `S_i`, to the
  diagonalizable group `D_{S_i}(Λ_i)` of some finitely generated abelian group `Λ_i`. This
  is Conrad's Definition B.1.1, not the field-level `IsMultiplicativeType` of
  [`Torus.MultiplicativeType`](MultiplicativeType.md).
- `Mono j.hom.hom`: the morphism `H.X ⟶ G.X` is a monomorphism in the category `Over S` of
  `S`-schemes. By the Yoneda lemma this says that for every `S`-scheme `T` the map
  `H(T) → G(T)` induced by `j` is injective.
- `IsClosedSubgroup j`: the underlying morphism of schemes `j.hom.hom.left` is a closed
  immersion.

## Statement and quantifiers

The proposition quantifies over every scheme `S`, all group schemes `G H : GroupScheme S`
with `IsAffineHom G.X.hom` and `LocallyOfFinitePresentation G.X.hom`, and every
homomorphism `j : H ⟶ G`. If `H` is of multiplicative type and `j.hom.hom` is a
monomorphism, then `j` is a closed immersion.

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I,
Panoramas et Synthèses 42–43, SMF, 2014. It is registered as
`conrad-2014-reductive-group-schemes`, file
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers are the
printed page numbers.

- Lemma B.1.3, p.281: "Let G be an S-affine S-group scheme of finite presentation and H an
  S-group of multiplicative type. Any monic homomorphism j : H → G is necessarily a closed
  immersion." The source adds that the lemma is SGA3 IX 2.5 (without finite presentation
  hypotheses) and a special case of SGA3 VIII 7.13(b).
- Definition B.1.1, p.280, defines `S`-groups of multiplicative type.

Conrad's proof (pp.281–283) reduces to a noetherian base, shows that `j` is proper by the
valuative criterion over a henselian discrete valuation ring over which `H` splits, and
concludes with EGA IV₃ 8.11.5 (a proper monomorphism of finite presentation is a closed
immersion). This is explanation only.

## Derivation from the source

- **Hypotheses on `G`.** "S-affine S-group scheme of finite presentation" is
  `IsAffineHom G.X.hom` and `LocallyOfFinitePresentation G.X.hom`. An affine morphism is
  quasi-compact and quasi-separated, so these two together are equivalent to `G → S` being
  affine and of finite presentation.
- **Group of multiplicative type.** `H` is any group scheme over `S` with
  `IsMultiplicativeType H`. The source does not assume `H` commutative separately, and
  neither does the statement.
- **Monic homomorphism.** A monic homomorphism of group schemes is a homomorphism that is a
  monomorphism of `S`-group functors, that is, injective on `T`-points for every
  `S`-scheme `T`. This is `Mono j.hom.hom`.
- **Closed immersion.** The conclusion is `IsClosedSubgroup j`.

## Scope

All schemes are in universe `u`. The base `S` is arbitrary, as in the source. The
statement does not cover the stronger SGA 3 versions without finite presentation or with
`G` only separated.

## Related Library statements

Several Library statements on relative maximal tori require the torus to be a closed
subgroup and cite Lemma B.1.3 to explain that this adds nothing. Examples are
`MaximalTorusSchemeStatement`
([`Torus.MaximalTorusSchemeStatement`](MaximalTorusSchemeStatement.md)) and
`WeylGroupSchemeFiniteEtaleStatement`
([`Torus.WeylGroupSchemeFiniteEtaleStatement`](WeylGroupSchemeFiniteEtaleStatement.md)).
Their tori are relative tori in the sense of `RelativeTorus.IsTorus`; this module does not
relate that predicate to `RelativeMultiplicativeType.IsMultiplicativeType`.
