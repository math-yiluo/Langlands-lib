# Statement: central quotients of reductive group schemes and their maximal tori

Worker 75.

`Langlands.GroupScheme.RelativeCentralQuotientStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It uses:

- `IsReductive` from [`Reductive.Basic`](Basic.md): a group scheme over a base `S` that
  is smooth and affine over `S`, and whose geometric fibres are connected reductive
  groups.
- `IsClosedSubgroup z` from [`Reductive.Basic`](Basic.md): the underlying morphism of
  schemes of `z` is a closed immersion.
- `IsCentral z` and `center G` from [`Rational.Characters`](../Rational/Characters.md):
  `center G` is the subgroup functor of all-test central points of `G` (a point `g` over
  `T` such that, for every `a : T' ⟶ T`, the restriction `a ≫ g` commutes with every
  point of `G` over `T'`), the functor of points of the scheme-theoretic centre `Z_G`.
  `IsCentral z` says that every point of `Z` maps into `center G`.
- `SubgroupFunctor.range` from [`SubgroupFunctor`](../SubgroupFunctor.md) and
  `SubgroupFunctor.comap` (written `F.comap q`) from
  [`Dynamic.Functoriality`](../Dynamic/Functoriality.md): on each test scheme, the points
  that factor through a given morphism, and the points whose image under `q` lies in
  `F`. The latter is the scheme-theoretic preimage.
- `RelativeRoot.IsFppfQuotient N q` from
  [`Rational.RootSubgroupStructureStatement`](../Rational/RootSubgroupStructureStatement.md):
  the underlying scheme morphism of `q` is flat, surjective and locally of finite
  presentation, and the range of the actual scheme kernel of `q` is `N` on every test
  scheme.
- `RelativeTorus.IsTorus` from [`Torus.Relative`](../Torus/Relative.md): a group scheme
  over `S` that becomes a split torus over the members of some étale cover of `S`.
- `IsFibrewiseMaximalTorus t` from
  [`Torus.FieldPointMaximality`](../Torus/FieldPointMaximality.md): the base change of `t`
  to every residue field of `S` is a maximal torus.
- Mathlib's `Flat`.

Inside the statement, a local abbreviation `IsMaxTorus t` for `t : T ⟶ H` with
`T` commutative means `RelativeTorus.IsTorus T`, `IsClosedSubgroup t` and
`IsFibrewiseMaximalTorus t`: `t` is a maximal torus of `H` over `S` in the sense of
Conrad's Definition 3.2.1.

## Statement

Let `S : Scheme.{u}` be any scheme, `G` a group scheme over `S` with `IsReductive G`,
`z : Z ⟶ G` a homomorphism with `IsClosedSubgroup z`, `IsCentral z` and `Z` flat over
`S`, and `q : G ⟶ G'` a homomorphism with
`RelativeRoot.IsFppfQuotient (SubgroupFunctor.range z) q`. Then:

1. **Reductivity.** `IsReductive G'`.
2. **Centre.** `(center G').comap q = center G`: the preimage under `q` of the centre
   of `G'` is the centre of `G`, i.e. the centre of `G'` is `Z_G/Z`.
3. **From `G` to `G'`.** For every maximal torus `t : T ⟶ G` there is a maximal torus
   `t' : T' ⟶ G'` with `(SubgroupFunctor.range t').comap q = SubgroupFunctor.range t`.
4. **From `G'` to `G`.** For every maximal torus `t' : T' ⟶ G'` there is a maximal
   torus `t : T ⟶ G` with `(SubgroupFunctor.range t').comap q = SubgroupFunctor.range t`.
5. **Uniqueness on `G'`.** Maximal tori `t₁, t₂` of `G'` with the same preimage under
   `q` have the same range.

## Source

Brian Conrad, *Reductive group schemes*, in *Autour des schémas en groupes* I, Panoramas
et Synthèses 42–43, SMF, 2014. It is registered as `conrad-2014-reductive-group-schemes`,
file `Conrad--Reductive group schemes (SGA3 notes)--2014.pdf` (SHA-256
`1a63a17e4ccb7e23263d65f05d93a6651262861e978e9eb0c1c53a01fd59140a`). Page numbers are
the printed page numbers.

- Corollary 3.3.5, p.100: "Let G be a reductive S-group scheme, and Z a multiplicative
  type subgroup scheme of the center Z_G. The reductive quotient G/Z has center Z_G/Z;
  in particular, G/Z_G has trivial center. Moreover, T ↦ T/Z defines a bijective
  correspondence between the set of maximal tori of G and the set of maximal tori of
  G/Z, with inverse given by scheme-theoretic preimage under the quotient map
  G → G/Z." Conrad notes that every such `T` contains `Z`, because `T = Z_G(T)`, and
  that the corollary is a special case of SGA3 XII 4.7(b),(c).
- Exercise 5.5.9(i), p.184: "Let G be a reductive group over a non-empty scheme S, and
  Z ⊂ Z_G a flat central closed subgroup scheme (so Z is of multiplicative type). […]
  (i) Prove that the smooth S-affine quotient G′ = G/Z is a reductive S-group, and that
  if T ⊂ G is a maximal torus (so Z ⊂ Z_G ⊂ Z_G(T) = T) then so is T′ := T/Z ⊂ G′.
  Give an example over a field in which T′ is split, T is non-split, and Z_G is not a
  direct factor of T." The omitted passage introduces parts (ii) and (iii).
- Definition 3.2.1, p.91 (maximal tori over a base: geometric fibres are maximal; Remark
  A.1.2 for actual fibres) and Theorem 3.3.4, p.98 (`Z_G` is flat
  over `S`).

Conrad proves Corollary 3.3.5 using Lemma 3.3.1. Exercise 5.5.9 is left to the reader.

## Derivation from the source

- **The subgroup `Z`.** The hypotheses on `z` follow Exercise 5.5.9: a flat central
  closed subgroup. By the exercise's parenthetical remark, such a `Z` is of
  multiplicative type, and every multiplicative type subgroup scheme of `Z_G` as in
  Corollary 3.3.5 is of this form. The flatness hypothesis is kept to match the source,
  although it also follows from the fppf quotient hypothesis, since `Z` is then the
  kernel of a flat morphism.
- **The quotient.** The statement does not construct `G/Z`. It quantifies over every
  homomorphism `q : G ⟶ G'` that is an fppf quotient of `G` by the range of `z`. Such a
  `q` is the quotient map `G → G/Z` of the source, up to unique isomorphism of `G'`.
  The source's assertion that `G/Z` is smooth and `S`-affine is part of
  `IsReductive G'`.
- **The centre.** "G/Z has center Z_G/Z" is clause 2: a point of `G` lies in the centre
  exactly when its image in `G'` does. Because `q` is an fppf surjection with kernel
  `Z ⊂ Z_G`, this identifies the centre of `G'` with the image `Z_G/Z`. The special case
  `Z = Z_G` (trivial centre of `G/Z_G`) is included.
- **Maximal tori.** Subgroups are recorded by the ranges of their inclusions. Clause 3
  is the second assertion of Exercise 5.5.9(i): the maximal torus `T'` with
  `q⁻¹(T') = T` is the image `T/Z`. Clauses 3–5 together are the bijection of
  Corollary 3.3.5: `T' ↦ q⁻¹(T')` is a well-defined bijection from the maximal tori of
  `G'` onto those of `G`, with inverse `T ↦ T/Z`.
- **Omitted.** The example over a field requested at the end of Exercise 5.5.9(i), and
  parts (ii) and (iii) of the exercise, are not stated. The non-emptiness of `S` in the
  exercise is not needed: over the empty scheme every clause holds trivially.

## Related Library statements

- `CentralQuotientReductiveStatement`
  ([`CentralQuotientReductiveStatement`](CentralQuotientReductiveStatement.md)) and
  `CenterQuotientReductiveStatement`, `CenterQuotientCenterTrivialStatement`
  ([`Adjoint/CenterQuotientStatement`](../Adjoint/CenterQuotientStatement.md)) state,
  over a field, that central quotients of connected reductive groups are connected
  reductive and that the quotient by the full centre has trivial centre.
