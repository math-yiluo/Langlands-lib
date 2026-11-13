# Statement: parabolic subgroups over affine schemes have Levi subgroups

Worker 75.

`Langlands.GroupScheme.RelativeLeviAffineExistenceStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It imports [`RelativeLevi.Basic`](Basic.md) (for
`IsRelativeParabolicSubgroup` and `IsRelativeLeviSubgroup`).

## Statement and quantifiers

The proposition quantifies over:

- every scheme `S : Scheme.{u}` with an instance `IsAffine S`;
- every pair of group schemes `G P : GroupScheme S`;
- every homomorphism `i : P ⟶ G`.

It has two hypotheses:

1. `IsReductive G` ([`Reductive.Basic`](../Reductive/Basic.md)): `G` is smooth and affine
   over `S` with connected reductive geometric fibres.
2. `IsRelativeParabolicSubgroup i` ([`RelativeLevi.Basic`](Basic.md)): `P` is smooth and
   affine over `S`, `i` is a monomorphism, and every residue fibre of `i` is a parabolic
   subgroup.

The conclusion is that there exist `L : GroupScheme S` and `l : L ⟶ P` with
`IsRelativeLeviSubgroup l`: `l` is a closed immersion, `L` is smooth over `S`, and for some
unipotent radical `r : U ⟶ P` the multiplication morphism `L ×_S U ⟶ P`,
`(x, u) ↦ l(x) r(u)`, is an isomorphism of `S`-schemes.

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I, Panoramas
et Synthèses 42–43, SMF, 2014; registered as `conrad-2014-reductive-group-schemes`, file
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers are the
one-based PDF pages, which agree with the printed page numbers of this file.

- Corollary 5.4.8, p.179: "If S is affine then P admits a Levi S-subgroup L and the
  natural map j_L : H¹(S_ét, L) → H¹(S_ét, P) is an isomorphism." The ambient setting is
  that of Definition 5.4.2, p.174: `G → S` is a reductive group scheme and `P ⊂ G` a
  parabolic subgroup.

## Derivation from the source

The proposition is the existence assertion of Corollary 5.4.8, with parabolic and Levi
subgroups as in [`RelativeLevi.Basic`](Basic.md). "S is affine" is the instance
`IsAffine S`. The second assertion, that `H¹(S_ét, L) → H¹(S_ét, P)` is bijective, is not
part of this proposition: the Library has no non-abelian étale cohomology of group
schemes to state it with.

## Scope

All objects are in universe `u`. The affine base `S` is otherwise arbitrary: it need not
be Noetherian, local, reduced or connected. No maximal torus, cocharacter or splitting is
assumed, and `P` need not be of the form `P_G(λ)` for a cocharacter over `S`.

## Relation to the Library

- Over a field, the published theorem `IsParabolicSubgroup.exists_isRationalLeviSubgroup`
  ([`Rational.LeviPreimageSolvableRadical`](../Rational/LeviPreimageSolvableRadical.md))
  gives a rational Levi subgroup of a parabolic subgroup of a connected reductive group,
  taking `ParabolicDynamicStatement` and `DynamicCentralizerReductiveStatement` as
  hypotheses.
- `RelativeLeviConjugacyStatement` ([`ConjugacyStatement`](ConjugacyStatement.md)) is the
  uniqueness counterpart: two Levi subgroups are conjugate under a unique point of the
  unipotent radical.

This module proves none of these relations.
