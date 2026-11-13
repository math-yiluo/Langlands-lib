# Statement: existence and uniqueness of the unipotent radical of a parabolic subgroup

Worker 75.

`Langlands.GroupScheme.RelativeUnipotentRadicalStatement.{u} : Prop` is a statement-only,
`Prop`-valued definition. This module does not prove it, and it adds no other definitions,
theorems or axioms. It imports [`RelativeLevi.Basic`](Basic.md) (for
`IsRelativeParabolicSubgroup` and `IsRelativeUnipotentRadical`).

## Statement and quantifiers

The proposition quantifies over:

- every scheme `S : Scheme.{u}`;
- every pair of group schemes `G P : GroupScheme S`;
- every group-scheme homomorphism `i : P ⟶ G`.

It has two hypotheses:

1. `IsReductive G` ([`Reductive.Basic`](../Reductive/Basic.md)): `G` is smooth and affine
   over `S`, and every geometric fibre is a connected reductive group (smooth, connected,
   affine, with trivial unipotent radical, over the chosen algebraic closure of the
   residue field).
2. `IsRelativeParabolicSubgroup i` ([`RelativeLevi.Basic`](Basic.md)): `P` is smooth and
   affine over `S`, `i` is a monomorphism, and every residue fibre `i_s` over `κ(s)` is a
   parabolic subgroup (`IsParabolicSubgroup`).

The conclusion has two parts.

- **Existence.** There are a group scheme `U : GroupScheme S` and a homomorphism
  `r : U ⟶ P` with `IsRelativeUnipotentRadical r`: `r` is a closed immersion, `U` is
  smooth over `S`, the image of `r` is normal in `P` on every test scheme, and for every
  point `s` of `S` the geometric fibre `r_{s̄} : U_{s̄} ⟶ P_{s̄}` satisfies the field
  predicate `IsUnipotentRadical`.
- **Uniqueness.** For every `U' : GroupScheme S` and `r' : U' ⟶ P` with
  `IsRelativeUnipotentRadical r'`, the subgroup functors `SubgroupFunctor.range r'` and
  `SubgroupFunctor.range r` are equal. `SubgroupFunctor.range r` assigns to each test
  `T : Over S` the subgroup of points `T ⟶ P.X` of the form `y ≫ r.hom.hom` with
  `y : T ⟶ U.X`. Equality of these functors on all `S`-schemes, including non-affine and
  nonreduced ones, is equality of the two closed subschemes of `P`.

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I, Panoramas
et Synthèses 42–43, SMF, 2014; registered as `conrad-2014-reductive-group-schemes`, file
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers are the
one-based PDF pages, which agree with the printed page numbers of this file.

- Corollary 5.2.5, p.153, first assertion: "Let G → S be a reductive group scheme, and
  P ⊂ G a parabolic subgroup. There is a unique smooth closed normal S-subgroup
  R_u(P) ⊂ P whose geometric fiber R_u(P)_s̄ coincides with the unipotent radical
  R_u(P_s̄) for all s ∈ S."
- Definition 5.2.1, p.151 (parabolic subgroups).

## Derivation from the source

The predicate `IsRelativeUnipotentRadical` of [`RelativeLevi.Basic`](Basic.md) is the
characterizing property in Corollary 5.2.5: smooth, closed, normal, with geometric fibres
the unipotent radicals. Over the algebraically closed field `κ(s)^alg`, the field predicate
`IsUnipotentRadical` asks for a smooth connected unipotent normal closed subgroup that
contains every such subgroup, which is the classical unipotent radical. The proposition
therefore states the first sentence of Corollary 5.2.5: the existence part is "there is a
... subgroup", and "unique" is expressed by equality of images as subgroup functors, since
two monomorphisms into `P` define the same subgroup exactly when their images agree on
every test scheme. Uniqueness is stated as equality of images rather than of the
homomorphisms because `U` and `r` are not given as subschemes of `P` but as abstract group
schemes with a closed immersion. The second paragraph of Corollary 5.2.5 (the quotient
`P/R_u(P)` is reductive, with a universal property) is not part of this proposition.

## Scope

All objects are in universe `u`. The base `S` is an arbitrary scheme. Parabolic subgroups
are not assumed closed in `G`; closedness is the separate statement
`RelativeParabolicClosedStatement` ([`ParabolicClosedStatement`](ParabolicClosedStatement.md)).
No maximal torus, cocharacter or splitting over `S` is assumed. The case `P = G` is
included; then `r` has trivial geometric fibres.

## Relation to the Library

- Over an algebraically closed field the uniqueness part follows from the published
  theorem `IsUnipotentRadical.range_eq`
  ([`Reductive.UnipotentRadical`](../Reductive/UnipotentRadical.md)); this proposition is
  the relative version over an arbitrary base.

This module proves none of these relations.
