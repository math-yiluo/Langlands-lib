# Statement: the quotient of a parabolic subgroup by its unipotent radical

Worker 75.

`Langlands.GroupScheme.RelativeParabolicReductiveQuotientStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It imports [`RelativeLevi.Basic`](Basic.md) (for
`IsRelativeParabolicSubgroup` and `IsRelativeUnipotentRadical`) and
[`Rational.RootSubgroupStructureStatement`](../Rational/RootSubgroupStructureStatement.md)
(for `RelativeRoot.IsFppfQuotient`).

## Statement and quantifiers

The proposition quantifies over:

- every scheme `S : Scheme.{u}`;
- all group schemes `G P U : GroupScheme S`;
- every group-scheme homomorphism `i : P ⟶ G`;
- every group-scheme homomorphism `r : U ⟶ P`.

It has three hypotheses:

1. `IsReductive G` ([`Reductive.Basic`](../Reductive/Basic.md)): `G` is smooth and affine
   over `S`, and every geometric fibre is a connected reductive group. That is, it is smooth,
   connected and affine with trivial unipotent radical over the chosen algebraic closure of
   the residue field.
2. `IsRelativeParabolicSubgroup i` ([`RelativeLevi.Basic`](Basic.md)): `P` is smooth and
   affine over `S`, `i` is a monomorphism, and every residue fibre `i_s` over `κ(s)` is a
   parabolic subgroup (`IsParabolicSubgroup`).
3. `IsRelativeUnipotentRadical r` ([`RelativeLevi.Basic`](Basic.md)): `r` is a closed
   immersion, `U` is smooth over `S`, the image of `r` is normal in `P` on every test
   scheme, and every geometric fibre `r_{s̄}` satisfies the field predicate
   `IsUnipotentRadical`.

The conclusion asserts that there are a group scheme `M : GroupScheme S` and a
homomorphism `q : P ⟶ M` with three properties.

- **Reductive.** `IsReductive M`.
- **Represented fppf quotient.** `RelativeRoot.IsFppfQuotient (SubgroupFunctor.range r) q`
  holds. That is, the morphism of schemes underlying `q` is flat, surjective and locally of
  finite presentation. Also, the range of the scheme-theoretic kernel inclusion `kernelι q`
  (the fibre of `q` over the identity section) equals `SubgroupFunctor.range r` on every
  test scheme over `S`. So `q` is an fppf covering whose kernel is the subgroup `r(U)`.
  This makes `M` represent the fppf quotient sheaf `P/U`. The proposition says nothing
  about the quotient of point groups `P(T)/U(T)` for a fixed test `T`.
- **Universal property.** For every `H : GroupScheme S` and every homomorphism
  `f : P ⟶ H` with `IsReductive H` and `Surjective f.hom.hom.left`, there is exactly one
  homomorphism `g : M ⟶ H` with `q ≫ g = f`. Here `Surjective f.hom.hom.left` means the
  morphism of schemes underlying `f` is surjective.

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I, Panoramas
et Synthèses 42–43, SMF, 2014. It is registered as `conrad-2014-reductive-group-schemes`,
file `Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). The page numbers
below are one-based PDF pages, and they match the printed page numbers in this file.

- Corollary 5.2.5, p.153, second paragraph: "The quotient P/R_u(P) is represented by a
  reductive group scheme, and any surjective homomorphism from P onto a reductive S-group
  uniquely factors through P/R_u(P)." The hypotheses are those of the first paragraph:
  "Let G → S be a reductive group scheme, and P ⊂ G a parabolic subgroup." R_u(P) is the
  unique smooth closed normal S-subgroup of P whose geometric fibres are the unipotent
  radicals R_u(P_s̄).
- The proof, pp.153–154, treats a surjective homomorphism `f : P ↠ G'` onto a reductive
  S-group and uses that `f` and its restriction to R_u(P) are fppf covers "by the fibral
  flatness criterion".
- Definition 5.2.1, p.151 (parabolic subgroups).

## Derivation from the source

- *R_u(P).* The proposition takes any `r` satisfying `IsRelativeUnipotentRadical`, which
  transcribes the defining property of R_u(P) in the first paragraph of Corollary 5.2.5.
  By the uniqueness in that paragraph, which is the separate proposition
  `RelativeUnipotentRadicalStatement` ([`UnipotentRadicalStatement`](UnipotentRadicalStatement.md)),
  every such `r` has the image R_u(P). Quantifying over all `r` therefore states the
  source's assertion for R_u(P) and nothing more. This proposition does not assume that
  first paragraph and does not depend on it.
- *"P/R_u(P) is represented by a reductive group scheme."* The quotient is the fppf
  quotient sheaf. A homomorphism `q : P ⟶ M` that is an fppf covering with kernel R_u(P)
  identifies `M` with this sheaf. This is the reading given by
  `RelativeRoot.IsFppfQuotient`, and `IsReductive M` adds that `M` is reductive.
- *"Any surjective homomorphism from P onto a reductive S-group uniquely factors through
  P/R_u(P)."* The proposition encodes "surjective" as surjectivity of the underlying
  morphism of schemes. The proof in the source uses exactly this: it gets the fppf
  covering property of `f` from the fibral flatness criterion. "Uniquely factors" means
  `∃! g : M ⟶ H, q ≫ g = f`, with `g` a homomorphism of group schemes.

## Scope

All objects are in universe `u`. The base `S` is an arbitrary scheme, including
non-noetherian and nonreduced ones. No maximal torus, cocharacter or splitting over `S` is
assumed. Parabolic subgroups are not assumed to be closed in `G`. The case `P = G` is
included; then `U` has trivial geometric fibres. No Levi subgroup of `P` is assumed, and the
proposition does not compare `M` with a Levi subgroup.

## Relation to the Library

- `RelativeUnipotentRadicalStatement` ([`UnipotentRadicalStatement`](UnipotentRadicalStatement.md))
  is the first paragraph of the same corollary: existence and uniqueness of R_u(P).
- `RelativeRoot.IsFppfQuotient` is the represented fppf quotient predicate that is also
  used, over a field, in `AffineNormalSubgroupQuotientStatement`
  ([`AffineNormalSubgroupQuotientStatement`](../AffineNormalSubgroupQuotientStatement.md)).

This module proves none of these relations.
