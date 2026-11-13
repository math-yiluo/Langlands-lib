# Statement: dynamic subgroups over any base scheme are finitely presented closed subgroups

Worker 3483.

`Langlands.GroupScheme.DynamicBaseRepresentabilityStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It imports [`Dynamic.Basic`](Basic.md) (for
`Dynamic.parabolic`, `Dynamic.unipotent`, `Dynamic.centralizer` and, through its imports,
`SubgroupFunctor.IsRepresentedBy`) and Mathlib's
`Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion` and
`Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation` (for `IsClosedImmersion` and
`LocallyOfFinitePresentation`).

## Statement and quantifiers

The proposition quantifies over:

- every scheme `S : Scheme.{u}`, not necessarily affine;
- every group scheme `G : GroupScheme S` whose structure morphism `G.X.hom` is
  `IsAffineHom` and `LocallyOfFinitePresentation` (instance arguments);
- every cocharacter `χ : (Gm S).toGrp ⟶ G`.

It asserts the conjunction of three existence claims, one for each of the subgroup functors
`F = Dynamic.parabolic χ`, `F = Dynamic.unipotent χ` and `F = Dynamic.centralizer χ`, in this
order: there exist a group scheme `H : GroupScheme S` and a homomorphism `j : H ⟶ G` such that

1. `IsClosedImmersion j.hom.hom.left`: the underlying morphism of schemes of `j` is a
   closed immersion;
2. `LocallyOfFinitePresentation H.X.hom`: the structure morphism `H → S` is locally of
   finite presentation;
3. `F.IsRepresentedBy j`.

- `Dynamic.parabolic χ`, `Dynamic.unipotent χ` and `Dynamic.centralizer χ` are the
  subgroup functors, on all schemes over `S`, of points `g` of `G` for which the orbit map
  `t ↦ χ(t) g χ(t)⁻¹` extends to the affine line, extends with value `1` at `0`, or is
  constant ([`Dynamic.Basic`](Basic.md)). They are defined over any base scheme. These are
  Conrad's `P_G(λ)`, `U_G(λ)` and `Z_G(λ)` for the conjugation action through `λ = χ`.
- `F.IsRepresentedBy j` ([`SubgroupFunctor`](../SubgroupFunctor.md)) says that `j` is a
  monomorphism of the underlying schemes over `S` and that the range of `j` is `F`: for every
  scheme `T` over `S`, the `T`-points of `G` that factor through `j` are exactly the points
  in `F`. So `H` represents `F` on all test schemes over `S`, not only affine ones.
- `IsAffineHom G.X.hom` says that the preimage of every affine open of `S` is affine. `G`
  itself need not be an affine scheme.

The trivial cocharacter is included.

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I,
Panoramas et Synthèses 42–43, SMF, 2014; registered as
`conrad-2014-reductive-group-schemes`, file
`Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers are
one-based PDF pages, which agree with the printed page numbers of this file.

- Theorem 4.1.7, p.112: "Let G be a finitely presented affine group over a ring k, and
  consider an action λ : Gm × G → G by the k-group Gm on the k-group G." Part 1: "These
  functors are unaffected by replacing λ with λⁿ for n > 0, and they are represented by
  respective finitely presented closed subgroups PG(λ), UG(λ), and ZG(λ) of G, with UG(λ)
  normalized by ZG(λ)."
- Right after the theorem, p.113: "When we apply Theorem 4.1.7 to examples in which the
  action arises from conjugation against a 1-parameter subgroup λ : Gm → G, we shall
  denote the resulting closed subgroups as PG(λ), UG(λ), and ZG(λ)."
- After Example 4.1.9, p.114: "It is immediate from the definitions that the formation of
  PG(λ), UG(λ), and ZG(λ) commutes with any base change on k, and that Theorem 4.1.7
  adapts to work over any base scheme S (not just affine schemes)."

## Derivation from the source

The Lean proposition is the representability assertion of Theorem 4.1.7(1), for the
conjugation action through a cocharacter, in the version over an arbitrary base scheme `S`
that Conrad states on p.114.

- Base and action. `S` is any scheme, as in Conrad's remark on p.114. The `G_m`-action is
  conjugation through `χ`, the case that Conrad writes `P_G(λ)`, `U_G(λ)`, `Z_G(λ)`. The
  Library's dynamic subgroups are defined only for this action.
- Hypotheses. Over a general base, the hypothesis "finitely presented affine group" of
  Theorem 4.1.7 reads: `G → S` is affine and of finite presentation. An affine morphism is
  quasi-compact and quasi-separated, so for an affine `G → S`, finite presentation is the
  same as local finite presentation. The Lean binders `IsAffineHom` and
  `LocallyOfFinitePresentation` therefore describe exactly Conrad's class of groups.
- Conclusion. "Represented by a finitely presented closed subgroup of `G`" is the existence
  of a homomorphism of group schemes `j : H ⟶ G` that is a closed immersion, with `H`
  finitely presented over `S`, representing the functor. A closed immersion is affine, so
  `H → S` is affine, hence quasi-compact and quasi-separated, and finite presentation of
  `H → S` is again local finite presentation. Representing the functor is
  `F.IsRepresentedBy j`; any two representatives are isomorphic over `G`, so asserting the
  existence of one is Conrad's assertion.
- Test schemes. Conrad defines the functors on `k`-algebras. The Library's functors are
  defined on all schemes over `S`; on an affine test scheme `Spec k'` they are Conrad's
  functors, read with Conrad's limit convention (an extension of the orbit map over the
  affine line exists, respectively exists with value `1` at `0`, respectively the orbit map
  is constant). A closed subscheme of `G` represents such a functor on all `S`-schemes as
  soon as it does on affine ones, because both a morphism to `H` and the extension of an
  orbit map (unique, as `G → S` is separated) can be checked and glued Zariski-locally on
  the test scheme. So the Lean conclusion is Conrad's representability.

So the proposition is the representability part of Conrad's Theorem 4.1.7(1) over a base
scheme, for conjugation actions, with Conrad's hypotheses.

## Scope

All objects are in universe `u`. The base `S` is arbitrary: it need not be affine,
Noetherian, quasi-compact or connected. Not stated here: the invariance under `λ ↦ λⁿ`
and the normalization of `U_G(λ)` by `Z_G(λ)` in part 1 (functor-level facts); the
abstract `G_m`-actions of Theorem 4.1.7; parts 2–4 of the theorem.

## Relation to the Library

- `Dynamic.Affine.isRepresentedBy_parabolicHom` and
  `Dynamic.Affine.isClosedSubgroup_parabolicHom`, and the same for the centralizer and the
  unipotent subgroup ([`Dynamic.AffineRepresentability`](AffineRepresentability.md)),
  construct closed representatives for a group scheme with affine underlying scheme over
  an affine base `Spec R`, with no finiteness hypothesis. They do not state finite
  presentation of the representatives, and they do not treat a non-affine base.
- The family 8 ledger (`notes/group-schemes/ledger-family-8-relative.md`, row F1) records
  the representability of `P(λ)`, `Z(λ)`, `U(λ)` over a non-affine base as having no Lean
  statement.

This module proves none of these relations.
