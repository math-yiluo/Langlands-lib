# Derived and central split factors of a maximal split torus

Author: Worker 1107.

This module declares
`Langlands.GroupScheme.DerivedCentralSplitTorusProductStatement.{u}` as a
Prop-valued definition. It states a structure assertion for actual group
schemes; it contains no proof of that assertion.

## Data and conclusion

The universe `u` and field `k : Type u` are arbitrary, including imperfect
fields and positive characteristic. All schemes, morphisms and test schemes
use the existing `Grp (Over (Spec k))` architecture.

The supplied data and hypotheses are:

- group schemes `G`, `D` and `d : D ⟶ G`, with `IsConnectedReductive G`
  and `IsDerivedSubgroup d`;
- commutative group schemes `S`, `S_D`, `A`, with
  `i : S.toGrp ⟶ G` and `j : S_D.toGrp ⟶ D` maximal split tori;
- a commutative-group-scheme morphism `e : S_D ⟶ S` whose underlying
  group homomorphism is a closed immersion, satisfying
  `j ≫ d = CommGroupScheme.groupHom e ≫ i`;
- a split component `a : A.toGrp ⟶ G`, meaning `IsSplitComponent a`, and
  a morphism `c : A ⟶ S` satisfying
  `CommGroupScheme.groupHom c ≫ i = a`.

The conclusion is `IsCentralIsogeny` for the actual multiplication
homomorphism

```text
S_D × A  →  S,       (x, y) ↦ e(x)c(y).
```

Lean uses the published `prodHom` on the underlying group schemes. Its
`comp_prodHom` formula gives precisely this multiplication on every test
scheme, including nonreduced tests. The commutativity proof passed to
`prodHom` uses the commutative group structure of `S`.

The predicate `IsCentralIsogeny` requires a finite, flat, surjective
scheme morphism, local finite presentation, and centrality of the full
scheme-theoretic kernel on every test scheme. It does not require the kernel
to be smooth or étale. Centrality here follows from commutativity of the
source product. The statement does not claim that multiplication is an
isomorphism or is surjective on `k`-points.

The meanings of the premises are inherited from
[`Derived.Basic`](Basic.md),
[`Rational.SplitTorus`](../Rational/SplitTorus.md) and
[`Rational.Characters`](../Rational/Characters.md). In particular,
`IsDerivedSubgroup d` is closedness and equality with the actual
scheme-theoretic derived subgroup functor on all tests. Split tori have
finite rank. Maximality is the absence of a proper larger closed split
torus through which the inclusion factors. `IsSplitComponent a` is
maximality among central closed split tori.

## Source and translation

This is a derived reformulation of Brian Conrad, Ofer Gabber and Gopal
Prasad, *Pseudo-reductive groups*, second edition (2015), registered source
`conrad-gabber-prasad-2015-pseudo-reductive`, SHA-256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.
The relevant original passages are:

- Definition C.2.11 and Remark C.2.12(2), printed pp.599–600 / PDF
  pp.625–626, and setup C.2.13, printed pp.599–601 / PDF pp.625–627;
- Theorem C.2.15, printed p.603 / PDF p.629, and Step 1 of its proof,
  printed p.604 / PDF p.630;
- Step 3, printed p.605 / PDF p.631, which obtains the same split-torus
  product from the isogeny category of tori;
- Definition A.1.11 and Example A.1.12, printed p.470 / PDF p.496,
  for the flat-surjective, finite scheme-theoretic kernel convention.

The source works with a smooth connected affine group and assumes
quasi-reductivity for this conclusion. A connected reductive group in the
published geometric sense has trivial geometric unipotent radical, hence
trivial `k`-unipotent radical and trivial `k`-split unipotent radical. Thus it
is quasi-reductive. Smoothness gives local finite presentation and
affineness gives quasi-compactness, so the finite-type scope of the source
is satisfied. No perfectness, characteristic or valued-field restriction
is introduced.

For the source's actual derived group, set
`S' = (S ∩ D(G))⁰_red`, and let `S₀` be its maximal central split torus.
Theorem C.2.15 and Step 1 say that `S'` is a maximal split torus of `D(G)`
and that `S` is the almost-direct product of `S'` and `S₀`. Thus the
multiplication `S' × S₀ → S` is an isogeny. These are split tori; the map
is finite faithfully flat, and it is locally of finite presentation
because it is a morphism between finite-type schemes over a field. Its
full kernel is central because the source is commutative. This is exactly
the `IsCentralIsogeny` convention used here.

The statement allows any supplied compatible factors, rather than naming
the source's canonical intersection. This uses the following transport
argument, which remains part of the future proof obligation. A supplied
closed split torus `S_D` in `D` with the displayed factorization through
`S` maps into `S ∩ D(G)`. Since it is reduced and connected, its map
factors through `(S ∩ D(G))⁰_red = S'`. That factor is a closed inclusion
of split tori in `D(G)`. Maximality of `j` makes it an isomorphism.
Likewise, every central split torus is contained in the unique maximal
central split torus `S₀`; maximality of `a` identifies its image with
`S₀`. The displayed compatibility of `c` with the closed ambient
inclusion `i` identifies `c` with this inclusion after transport. Its
closedness follows from that of `a` and `i`; it need not be added as a
premise. Finally, any supplied `d` satisfying `IsDerivedSubgroup` is
uniquely isomorphic over `G` to the source's derived subgroup because
both represent the same all-test subgroup functor. Transport by these
isomorphisms preserves the asserted multiplication isogeny.

This translation explains why the supplied maximality and compatibility
premises do not assume the product conclusion. The source's larger
quasi-reductive scope is not asserted by this declaration.

No retained source errata file was found in the checked project,
workspace or supplied Library directories. The author-hosted book page
was also checked on 3 November 2026: it displayed no second-edition
errata, and its commented historical `predtypo.pdf` link returned HTTP
404. This is a bounded source check.

## Existing interfaces and remaining obligations

The published
[`DerivedMaximalSplitTorusStatement`](MaximalSplitTorusStatement.md)
separately asserts existence of suitable `S_D`, `j` and `e`; the current
statement uses supplied such data and adds the product conclusion. The
published
`IsSplitComponent.exists_commFactor_of_isMaximalSplitTorus` in
[`Rational.SplitCentralEmbedding`](../Rational/SplitCentralEmbedding.md)
supplies a closed compatible `c` for every supplied split component.
Neither result is redefined here. Existence of a split component is also
a separate obligation.

The possibly nonsplit central-torus-times-derived-group surjectivity
target concerns a product mapping to `G`; it does not assert this
product inside the actual split torus `S`. The present declaration
does not construct a simply connected cover, assert a cocharacter
decomposition, or prove an apartment comparison. Its proof and the
applications of that proof remain separate.
