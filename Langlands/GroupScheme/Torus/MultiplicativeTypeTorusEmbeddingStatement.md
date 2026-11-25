# Statement: groups of multiplicative type embed in tori

`Langlands.GroupScheme.MultiplicativeTypeTorusEmbeddingStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It imports:

- [`Torus.RelativeMultiplicativeType`](RelativeMultiplicativeType.md), for the relative
  predicate `RelativeMultiplicativeType.IsMultiplicativeType` (Conrad, Definition B.1.1);
- [`Torus.Relative`](Relative.md), for the relative torus predicate
  `RelativeTorus.IsTorus`;
- [`Reductive.Basic`](../Reductive/Basic.md), for `IsClosedSubgroup`.

`GroupScheme S` is `Grp (Over S)`, and a morphism `H ⟶ T` in it is a homomorphism of group
schemes over `S`.

## Predicates used

- `RelativeMultiplicativeType.IsMultiplicativeType H`, for `H : GroupScheme S`: there is an
  fppf cover of `S` (a jointly surjective family of flat morphisms `S_i ⟶ S` locally of
  finite presentation) such that each base change `H_{S_i}` is isomorphic, as a group
  scheme over `S_i`, to the diagonalizable group `D_{S_i}(Λ_i)` of some finitely generated
  abelian group `Λ_i`. This is Conrad's Definition B.1.1.
- `RelativeTorus.IsTorus T`, for `T : GroupScheme S`: there is a jointly surjective étale
  cover of `S`, indexed in universe `u`, on each member of which the base change of `T` is
  a split torus (`IsSplitTorus`); the rank may vary between members.
- `IsClosedSubgroup i`, for `i : H ⟶ T`: the underlying morphism of schemes
  `i.hom.hom.left` is a closed immersion.

## Statement and quantifiers

The proposition quantifies over every scheme `S` and every `H : GroupScheme S` with
`RelativeMultiplicativeType.IsMultiplicativeType H`. It asserts that there exist a group
scheme `T : GroupScheme S` and a homomorphism `i : H ⟶ T` such that
`RelativeTorus.IsTorus T` and `IsClosedSubgroup i`.

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I,
Panoramas et Synthèses 42–43, SMF, 2014. It is registered as
`conrad-2014-reductive-group-schemes`, file
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers are the
printed page numbers.

- Proposition B.3.8, p.295: "Let H → S be a group scheme of multiplicative type. There
  exists an S-torus T such that H is a closed S-subgroup of T."
- Definition B.1.1, p.280: "A group scheme G → S is of multiplicative type if there is an
  fppf covering {S_i} of S such that G_{S_i} ≃ D_{S_i}(M_i) for a finitely generated abelian
  group M_i for each i."
- Paragraph before Proposition B.3.8, p.295: "every fppf closed subgroup scheme of a torus
  is of multiplicative type" (from Corollary B.3.3), and Proposition B.3.8 is "a converse
  result".

Conrad's proof (pp.296–297) writes `H` as an extension of a finite multiplicative type group
`H'` by a torus, splits the extension after a finite étale base change, embeds the finite
part `D_S(M)` into the torus `D_S(F)` for a surjection `F ↠ M` from a finitely generated
free `ℤ`-module, and descends the embedding with Weil restriction along the finite étale
cover. This is explanation only.

## Derivation from the source

- **Group of multiplicative type.** Definition B.1.1, the relative
  `RelativeMultiplicativeType.IsMultiplicativeType`.
- **S-torus.** Conrad's Definition 3.1.1 (p.81): "An S-torus is an S-group T → S of
  multiplicative type with smooth connected fibers", and on the same page: "By Proposition
  B.3.4, any S-torus becomes a power of G_m étale-locally on S". The proposition uses the
  Library's étale form `RelativeTorus.IsTorus`, as do the other relative torus statements of
  the Library. The rank may vary between members of the splitting cover, as it may for an
  `S`-torus over a disconnected base.
- **Closed S-subgroup.** "H is a closed S-subgroup of T" means that there is a homomorphism
  `i : H ⟶ T` of group schemes over `S` whose underlying morphism of schemes is a closed
  immersion (`IsClosedSubgroup i`). The torus `T` and the embedding `i` are existentially
  quantified, as in the source.

## Scope

All schemes are in universe `u`. The base `S` is arbitrary, as in the source. The
preliminary claim in Conrad's proof, that `H` is uniquely an extension of a finite group of
multiplicative type by a torus, is not stated.
