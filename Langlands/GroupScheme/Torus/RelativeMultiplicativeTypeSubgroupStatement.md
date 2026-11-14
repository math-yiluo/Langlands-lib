# Statement: fppf closed subgroups of groups of multiplicative type

Worker 75.

`Langlands.GroupScheme.RelativeMultiplicativeTypeClosedSubgroupStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It imports:

- [`Torus.RelativeMultiplicativeType`](RelativeMultiplicativeType.md), for the relative
  predicate `RelativeMultiplicativeType.IsMultiplicativeType` (Conrad, Definition B.1.1);
- [`Reductive.Basic`](../Reductive/Basic.md), for `IsClosedSubgroup`.

`GroupScheme S` is `Grp (Over S)`, and a morphism `H ⟶ H'` in it is a homomorphism of group
schemes over `S`.

## Predicates used

- `RelativeMultiplicativeType.IsMultiplicativeType H`, for `H : GroupScheme S`: there is an
  fppf cover of `S` (a jointly surjective family of flat morphisms `S_i ⟶ S` locally of
  finite presentation) such that each base change `H_{S_i}` is isomorphic, as a group
  scheme over `S_i`, to the diagonalizable group `D_{S_i}(Λ_i)` of some finitely generated
  abelian group `Λ_i`. This is Conrad's Definition B.1.1.
- `IsClosedSubgroup i`, for `i : H ⟶ H'`: the underlying morphism of schemes
  `i.hom.hom.left` is a closed immersion.
- `Flat H.X.hom` and `LocallyOfFinitePresentation H.X.hom`: the structure morphism
  `H → S` is flat and locally of finite presentation.

## Statement and quantifiers

The proposition quantifies over every scheme `S`, all group schemes `H H' : GroupScheme S`
and every homomorphism `i : H ⟶ H'`. Under the hypotheses

1. `RelativeMultiplicativeType.IsMultiplicativeType H'`,
2. `IsClosedSubgroup i`,
3. `Flat H.X.hom`,
4. `LocallyOfFinitePresentation H.X.hom`,

it concludes `RelativeMultiplicativeType.IsMultiplicativeType H`.

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I,
Panoramas et Synthèses 42–43, SMF, 2014. It is registered as
`conrad-2014-reductive-group-schemes`, file
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers are the
printed page numbers.

- Corollary B.3.3, p.290: "Let S be a scheme and H′ an S-group of multiplicative type. Any
  fppf closed subgroup H ⊂ H′ is of multiplicative type."
- Definition B.1.1, p.280: "A group scheme G → S is of multiplicative type if there is an
  fppf covering {S_i} of S such that G_{S_i} ≃ D_{S_i}(M_i) for a finitely generated abelian
  group M_i for each i."

Conrad's proof (p.290) passes to an fppf cover on which `H' = D_S(M)`, reduces to a complete
local noetherian base, lifts the special fibre `H_k = D_k(M/N)` with Theorem B.3.2, and
shows that the quotient by `D_S(M/N)` is trivial. This is explanation only.

## Derivation from the source

- **Group of multiplicative type.** Conrad's "S-group of multiplicative type" is the
  relative predicate `RelativeMultiplicativeType.IsMultiplicativeType` of Definition B.1.1,
  not the field-level `IsMultiplicativeType` of
  [`Torus.MultiplicativeType`](MultiplicativeType.md).
- **Closed subgroup `H ⊂ H'`.** A closed subgroup is a group scheme `H` over `S` with a
  homomorphism `i : H ⟶ H'` whose underlying morphism of schemes is a closed immersion
  (`IsClosedSubgroup i`). This is the Library's usual encoding of closed subgroup schemes.
- **fppf.** "fppf" in "fppf closed subgroup" means that `H` is flat and locally of finite
  presentation over `S`; these are hypotheses 3 and 4.

## Scope

All schemes are in universe `u`. The base `S` is arbitrary, as in the source. The
homomorphism `i` is not required to be normal or central, and no condition on the fibres of
`H` is imposed.
