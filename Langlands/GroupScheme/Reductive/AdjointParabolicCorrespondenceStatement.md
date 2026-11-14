# Statement: parabolic subgroups of a reductive group and of its adjoint quotient

Worker 75.

`Langlands.GroupScheme.AdjointParabolicCorrespondenceStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It uses:

- `IsReductive` from [`Reductive.Basic`](Basic.md): a group scheme over a base `S` that
  is smooth and affine over `S`, and whose geometric fibres are connected reductive
  groups.
- `center G` from [`Rational.Characters`](../Rational/Characters.md): the subgroup
  functor of all-test central points of `G`. A point `g` over `T` lies in it when, for
  every `a : T' ⟶ T`, the restriction `a ≫ g` commutes with every point of `G` over
  `T'`. This is the functor of points of the scheme-theoretic centre `Z_G`.
- `SubgroupFunctor.range i` from [`SubgroupFunctor`](../SubgroupFunctor.md): on each
  test scheme, the points of `G` that factor through `i`. The order `≤` on subgroup
  functors is inclusion on every test scheme.
- `SubgroupFunctor.comap q F` (written `F.comap q`) from
  [`Dynamic.Functoriality`](../Dynamic/Functoriality.md): on each test scheme, the
  points `x` of `G` with `x ≫ q` in `F`. This is the scheme-theoretic preimage.
- `RelativeRoot.IsFppfQuotient N q` from
  [`Rational.RootSubgroupStructureStatement`](../Rational/RootSubgroupStructureStatement.md):
  the underlying scheme morphism of `q` is flat, surjective and locally of finite
  presentation, and the range of the actual scheme kernel of `q` is `N` on every test
  scheme.
- `IsRelativeParabolicSubgroup i` from [`RelativeLevi.Basic`](../RelativeLevi/Basic.md):
  `P` is smooth and affine over `S`, `i : P ⟶ G` is a monomorphism of `S`-schemes, and
  every residue fibre of `i` is a parabolic subgroup.
- `IsRelativeBorelSubgroup i` from [`RelativeLevi.Borel`](../RelativeLevi/Borel.md): a
  relative parabolic subgroup whose residue fibres are Borel subgroups that stay Borel
  over an algebraic closure.

## Statement

Let `S : Scheme.{u}` be any scheme and `G` a group scheme over `S` with
`IsReductive G`. Then:

1. **The centre lies in every parabolic.** For every `i : P ⟶ G` with
   `IsRelativeParabolicSubgroup i`, `center G ≤ SubgroupFunctor.range i`.

Moreover, for every group scheme `Gad` over `S` and every `q : G ⟶ Gad` with
`RelativeRoot.IsFppfQuotient (center G) q`:

2. **From `G` to `Gad`.** For every relative parabolic subgroup `i : P ⟶ G` there is a
   relative parabolic subgroup `i' : P' ⟶ Gad` with
   `(SubgroupFunctor.range i').comap q = SubgroupFunctor.range i`.
3. **From `Gad` to `G`.** For every relative parabolic subgroup `i' : P' ⟶ Gad` there
   is a relative parabolic subgroup `i : P ⟶ G` with
   `(SubgroupFunctor.range i').comap q = SubgroupFunctor.range i`.
4. **Uniqueness on `Gad`.** If `i₁ : P₁ ⟶ Gad` and `i₂ : P₂ ⟶ Gad` are relative
   parabolic subgroups with the same preimage under `q`, then they have the same range.
5. **Borel subgroups.** If `i : P ⟶ G` and `i' : P' ⟶ Gad` are relative parabolic
   subgroups with `(SubgroupFunctor.range i').comap q = SubgroupFunctor.range i`, then
   `IsRelativeBorelSubgroup i ↔ IsRelativeBorelSubgroup i'`.

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I, Panoramas
et Synthèses 42–43, SMF, 2014. It is registered as `conrad-2014-reductive-group-schemes`,
file `Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers are
the printed page numbers.

- Exercise 5.5.8, p.184: "Let G be a reductive group over a scheme S. Show that if P is
  a parabolic subgroup of G then Z_G ⊂ P and that P ↦ P/Z_G is a bijective
  correspondence between the sets of parabolic subgroups of G and of G^ad = G/Z_G, with
  inverse given by the formation of inverse images under the quotient map G → G^ad.
  Construct natural isomorphisms Par_{G/S} ≃ Par_{G^ad/S} and Bor_{G/S} ≃ Bor_{G^ad/S}."
- Definition 5.2.1, p.151 (parabolic subgroups) and Definition 5.2.10, p.157: "A Borel
  subgroup of a reductive group scheme G → S is a parabolic subgroup P ⊂ G such that
  P_s is a Borel subgroup of G_s for all s ∈ S."
- Theorem 3.3.4, p.98: the scheme-theoretic centre `Z_G` of a reductive group scheme
  is represented by a closed subgroup scheme, flat over `S` and of multiplicative type.

Conrad leaves the exercise to the reader; the notes contain no proof of it.

## Derivation from the source

- **The adjoint quotient.** The statement does not construct `G^ad = G/Z_G`. It
  quantifies over every homomorphism `q : G ⟶ Gad` that is an fppf quotient of `G` by
  its centre in the sense of `RelativeRoot.IsFppfQuotient (center G) q`. Such a `q` is
  the quotient map `G → G/Z_G` of the source, up to unique isomorphism of the target.
  If no such `q` existed, clauses 2–5 would hold vacuously; clause 1 does not depend
  on `q`.
- **Subgroups as ranges.** A parabolic subgroup is a subscheme of `G`, so it is
  recorded by the range of its inclusion. Clause 1 is `Z_G ⊂ P` on points over every
  test scheme.
- **The bijection.** Conrad's map sends `P` to `P/Z_G`, the image of `P` in `G^ad`, and
  its inverse sends `P'` to the preimage `q⁻¹(P')`. Clause 2 says that every `P` is the
  preimage of a parabolic subgroup `P'` of `G^ad`. Because `q` is an fppf surjection
  whose kernel `Z_G` lies in `P`, such a `P'` is the image `P/Z_G`. Clause 3 says that
  the preimage of every parabolic subgroup of `G^ad` is a parabolic subgroup of `G`.
  Clause 4 says that `P'` is determined by `q⁻¹(P')`. Together, clauses 2–4 say that
  `P' ↦ q⁻¹(P')` is a well-defined bijection from the parabolic subgroups of `G^ad`
  onto those of `G`; its inverse is `P ↦ P/Z_G`.
- **Borel subgroups.** Clause 5 says that the bijection matches Borel subgroups with
  Borel subgroups. This is the part of the bijection that underlies the requested
  isomorphism `Bor_{G/S} ≃ Bor_{G^ad/S}`.
- **Omitted.** The statement does not construct the isomorphisms of the schemes
  `Par_{G/S} ≃ Par_{G^ad/S}` and `Bor_{G/S} ≃ Bor_{G^ad/S}`. Their naturality amounts
  to compatibility of the bijection with base change on `S`, which is also not stated.
- **No extra hypotheses.** `S` is arbitrary. Parabolic subgroups are only required to
  be monomorphisms, following the Library predicate; Conrad proves in Proposition
  5.2.3 (p.152) that they are closed.

## Related Library statements

- `ReductiveDerivedTorusParabolicCorrespondenceStatement`
  ([`DerivedTorusParabolicCorrespondenceStatement`](DerivedTorusParabolicCorrespondenceStatement.md))
  is the analogous correspondence for the derived group (Conrad Proposition 5.3.4).
- `CenterQuotientReductiveStatement`
  ([`Adjoint/CenterQuotientStatement`](../Adjoint/CenterQuotientStatement.md)) states,
  over a field, that the quotient of a connected reductive group by its centre is
  connected reductive.
