# Statement: centralizers of subgroups of multiplicative type over a general base

`Langlands.GroupScheme.RelativeMultiplicativeTypeCentralizerStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It imports:

- [`Torus.RelativeMultiplicativeType`](RelativeMultiplicativeType.md), for the relative
  predicate `RelativeMultiplicativeType.IsMultiplicativeType` (Conrad, Definition B.1.1);
- [`Rational.TorusCentralizer`](../Rational/TorusCentralizer.md), for the all-test
  centralizer functor `torusCentralizer`;
- [`Reductive.Basic`](../Reductive/Basic.md), for `IsClosedSubgroup`, `IsReductive` and
  `IsConnectedReductive`;
- [`RelativeIdentityComponent`](../RelativeIdentityComponent.md), for
  `IsRelativeIdentityComponent` and `RelativeIdentityComponent.residueFiber`.

`GroupScheme S` is `Grp (Over S)`, and `CommGroupScheme S` is the category of commutative
group schemes over `S`, with underlying group scheme `H.toGrp`. Inside the definition the
namespace `RelativeMultiplicativeType` is open, so `IsMultiplicativeType` is the relative
predicate, not the field-level one of [`Torus.MultiplicativeType`](MultiplicativeType.md).

## Predicates used

- `IsMultiplicativeType H.toGrp`: there is an fppf cover of `S` (a jointly surjective
  family of flat morphisms locally of finite presentation) over each member of which `H`
  becomes isomorphic to `D(Λ)` for a finitely generated abelian group `Λ`.
- `IsClosedSubgroup i`: the morphism of schemes underlying `i` is a closed immersion.
- `torusCentralizer i : SubgroupFunctor G` is the centralizer functor `Z_G(H)`. A point
  `g : U ⟶ G.X` over `S` belongs to it when, for every `a : V ⟶ U` over `S` and every point
  `t : V ⟶ H.X`, the points `a ≫ g` and `t ≫ i` of `G` commute. Despite its name the
  definition applies to any commutative group scheme `H` and any homomorphism `i`.
- `F.IsRepresentedBy z`, for `z : Z ⟶ G`: the morphism underlying `z` is a monomorphism
  and the subgroup functor of points factoring through `z` equals `F`. Closedness is not
  part of this predicate.
- `IsReductive Z₀` (Conrad, Definition 3.1.1): `Z₀ → S` is smooth and affine and its
  geometric fibres are connected reductive.
- `IsRelativeIdentityComponent Z z₀`: `z₀ : Z₀ ⟶ Z` is an open immersion, and a point of
  `Z` over any test scheme factors through `z₀` exactly when its image in every residue
  fibre `Z_s` lies in the identity component of `Z_s`. So `Z₀` represents the relative
  identity component `Z⁰`, the union of the identity components of the fibres.
- `RelativeIdentityComponent.residueFiber Z₀ s` is the fibre `Z₀_s` over the residue field
  `κ(s)`. `IsConnectedReductive` of a group over a field `k` means smooth, affine and
  connected, with trivial unipotent radical after base change to an algebraic closure of
  `k`.

## Statement and quantifiers

For every scheme `S`, every group scheme `G` over `S` with `G → S` affine and locally of
finite presentation, every commutative group scheme `H` over `S` with
`IsMultiplicativeType H.toGrp`, and every homomorphism `i : H ⟶ G` that is a closed
immersion, the following three assertions hold.

1. **Representability.** There are a group scheme `Z` over `S` and a homomorphism
   `z : Z ⟶ G` that is a closed immersion, with `Z → S` locally of finite presentation,
   such that `z` represents `torusCentralizer i`.
2. **Smoothness.** If `G → S` is smooth, then for every group scheme `Z` and homomorphism
   `z : Z ⟶ G` representing `torusCentralizer i`, `Z → S` is smooth.
3. **Reductive identity component.** If `G` is reductive, then for every `z : Z ⟶ G`
   representing `torusCentralizer i` and every `z₀ : Z₀ ⟶ Z` with
   `IsRelativeIdentityComponent Z z₀`: `Z₀` is reductive, `z₀` is a closed immersion, and
   for every `s ∈ S` the fibre `Z₀_s` is connected reductive over `κ(s)`.

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I,
Panoramas et Synthèses 42–43, SMF, 2014. It is registered as
`conrad-2014-reductive-group-schemes`, file
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers are the
printed page numbers.

- Lemma 2.2.4, pp.64–65: "Let G → S be a finitely presented S-affine S-group, and Y a
  finitely presented closed subscheme of G. Assume that Y is a subgroup of multiplicative
  type or that Y → S either is smooth with each fiber non-empty and connected … or is finite
  flat. Then Z_G(Y) exists as a finitely presented closed subgroup; it is smooth when G is
  smooth and Y is a subgroup of multiplicative type, in which case
  Lie(Z_G(Y)) = Lie(G)^Y …" Conrad adds that for `G` smooth and `Y` a subgroup of
  multiplicative type the lemma is part of SGA3 XI 5.3, aside from the description of
  `Lie(Z_G(Y))`.
- Remark 3.1.5, p.83: "Let H be a multiplicative type subgroup of a reductive S-group G. …
  Nonetheless, Z_G(H) is smooth (by Lemma 2.2.4) and the geometric fibers Z_G(H)_s have
  reductive identity component (by [CGP, A.8.12] …). The fibers of Z_G(H) can be
  disconnected. By Proposition 3.1.3, the open subgroup Z_G(H)⁰ is reductive (hence affine)
  over S and closed in Z_G(H)."
- Definition B.1.1, p.280, defines S-groups of multiplicative type; Definition 3.1.1, p.81,
  defines reductive S-groups.

The proof of Lemma 2.2.4 writes `Z_G(H)` as the intersection of the centralizers of the
finite flat torsion subgroups `H[n]`, each represented through the Hom-scheme of
Lemma 2.1.3, and proves smoothness by the infinitesimal criterion and the vanishing of
Hochschild cohomology. Remark 3.1.5 obtains the fibre assertion from Conrad–Gabber–Prasad
A.8.12 and the last sentence from Proposition 3.1.3 (the Library's
`IdentityComponentClopenStatement`). This is explanation only.

## Derivation from the source

- **Hypotheses.** "Finitely presented S-affine S-group" is `IsAffineHom G.X.hom` and
  `LocallyOfFinitePresentation G.X.hom`; an affine morphism is quasi-compact and
  quasi-separated, so together they give finite presentation. The closed subscheme `Y` is
  the image of the closed immersion `i` from a group `H` of multiplicative type. `H` is
  taken commutative, as every group of multiplicative type is. Finite presentation of `Y`
  is not assumed separately: a group of multiplicative type is finitely presented over
  `S`, since `D(Λ)` is for finitely generated `Λ` and finite presentation descends along
  fppf covers.
- **Part 1.** "Z_G(Y) exists as a finitely presented closed subgroup" is representability
  of the centralizer functor by a closed subgroup `z`, with `Z → S` locally of finite
  presentation. `Z` is closed in the `S`-affine `G`, so it is `S`-affine and hence finitely
  presented.
- **Part 2.** "It is smooth when G is smooth and Y is a subgroup of multiplicative type" is
  stated for every representing subgroup. All representing subgroups are isomorphic over
  `G`, so this is equivalent to smoothness of the one from part 1.
- **Part 3.** A reductive `G` is smooth and affine and hence finitely presented, so the
  hypotheses of parts 1 and 2 hold. "The geometric fibers Z_G(H)_s have reductive identity
  component" is the fibre clause: the fibre `Z₀_s` is the identity component of `Z_s` by the
  definition of the relative identity component, and a group over `κ(s)` is connected
  reductive exactly when its geometric fibre is. "Z_G(H)⁰ is reductive over S and closed in
  Z_G(H)" is `IsReductive Z₀` and the closed immersion `z₀`. The open subgroup `Z_G(H)⁰` is
  any `z₀` with `IsRelativeIdentityComponent Z z₀`. The relative identity component of a
  smooth group scheme exists (`RelativeIdentityComponent.smoothExistence` in
  [`RelativeIdentityComponent/SmoothExistenceProof`](../RelativeIdentityComponent/SmoothExistenceProof.md)),
  so part 3 is not vacuous.

## Scope and omissions

All schemes are in universe `u`. The statement covers the multiplicative-type case of
Lemma 2.2.4 except the description of `Lie(Z_G(H))`, which needs a Lie algebra of a group
scheme over a general base. The other cases of the lemma (`Y` smooth with connected
fibres, or finite flat, and not necessarily a subgroup) are not stated. From Remark 3.1.5
it omits the remarks that `H` need not lie in a maximal torus and that the fibres of
`Z_G(H)` can be disconnected, which are not assertions about all `H`.

## Related Library statements

- `RelativeTorusCentralizerReductiveStatement`
  ([`Torus.RelativeCentralizerReductiveStatement`](RelativeCentralizerReductiveStatement.md))
  is the torus case: for a closed `S`-torus in a reductive `G`, the centralizer is
  represented by a closed subgroup and is reductive.
- `MultiplicativeTypeCentralizerReductiveStatement`
  ([`Torus.MultiplicativeTypeCentralizerReductiveStatement`](MultiplicativeTypeCentralizerReductiveStatement.md))
  is the case of a base field.
- [`Torus.RelativeCentralizerSmooth`](RelativeCentralizerSmooth.md) proves smoothness of
  centralizers of diagonalizable groups acting on smooth affine groups over an affine
  base.
- `IdentityComponentClopenStatement`
  ([`Reductive.IdentityComponentClopenStatement`](../Reductive/IdentityComponentClopenStatement.md))
  is Conrad's Proposition 3.1.3, used for the last sentence of Remark 3.1.5.
