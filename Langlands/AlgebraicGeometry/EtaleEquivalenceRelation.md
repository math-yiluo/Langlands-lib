# Étale equivalence relations on schemes

Authors: Worker 239 and Worker 266. Worker 239 wrote the Lean declarations
and the first version of this Markdown. Worker 266 checked both against the
cited sources and corrected the provenance notes.

This module defines étale equivalence relations on schemes, the property that
such a relation has an affine quotient, cartesian morphisms of étale
equivalence relations, and the existence of a finite surjective cartesian
cover by a relation with an affine quotient. Algebraic spaces can be presented
by these data (Stacks Theorem 65.10.5). The definitions are the vocabulary for
a reduction of Stacks Lemma 70.15.1 (Tag 07VS, the published
`FiniteSurjectiveAffineDescentStatement`) to statements about presentations.
This module states and proves no theorem.

It imports only Mathlib: `AlgebraicGeometry.Limits` (finite limits of schemes,
for the product `U × U`) and the morphism-property modules for étale, finite,
flat, locally finitely presented and surjective morphisms. Mathlib is pinned
at commit `5ed2965256430c3649e86755f9576b54eca72435` by the prepared
environment.

## Sources and provenance

The retained original is the registered Stacks Project HTML snapshot
`stacks-etale-equivalence-relations-2026-11-01` (directory SHA-256
`df1ecbfa63c5e31cf736d9ea79dd262976c3098fd9b36f2dd32668d44bf75420`), downloaded
on 1 November 2026 with comments. Each page has a same-stem text aid, and the
folder's `README.md` summarizes every page:

- `022P.html`, [Definition 39.3.1](https://stacks.math.columbia.edu/tag/022P):
  relations and equivalence relations `j = (t, s) : R → U ×_S U`, with
  `t = pr₀ ∘ j` and `s = pr₁ ∘ j`. Comments #6527 and #6528 confirm that an
  equivalence relation is a relation (a monomorphism) that is a
  pre-equivalence relation.
- `02WS.html`, [Definition 65.9.2](https://stacks.math.columbia.edu/tag/02WS):
  an étale equivalence relation is an equivalence relation whose projections
  `s` and `t` are étale.
- `0263.html` and `02WW.html`,
  [Definition 65.9.3](https://stacks.math.columbia.edu/tag/0263) and
  [Theorem 65.10.5](https://stacks.math.columbia.edu/tag/02WW): presentations,
  and the theorem that the fppf quotient `U/R` of an étale equivalence
  relation is an algebraic space with `U → U/R` étale and surjective.
- `02VG.html`, `03BD.html` and `03C5.html`,
  [Definitions 39.20.1, 39.20.2](https://stacks.math.columbia.edu/tag/03BD) and
  [Lemma 39.20.3](https://stacks.math.columbia.edu/tag/03C5): the quotient
  sheaf, representable quotients, and the representability criterion. The
  tag page `03C5.html` shows only the lemma.
- `045Y.html`, [Lemma 39.20.4](https://stacks.math.columbia.edu/tag/045Y):
  two points of `U` have the same image in `U/R` exactly when they are related
  by `R` locally.
- `0APD.html` and `07S3.html`,
  [Definition 39.21.1](https://stacks.math.columbia.edu/tag/0APD) and
  [Lemma 39.20.7](https://stacks.math.columbia.edu/tag/07S3): cartesian
  morphisms, and the fibre-product criterion for quotients of equivalence
  relations.

All of these pages and their comments were read. No comment changes a
definition used here, and no errata note exists for the source.

Two further registered sources are cited:

- `stacks-groupoid-schemes-chapter-pdf-2026-07-14`, the Groupoid Schemes
  chapter PDF built on 14 July 2026 (file SHA-256
  `4506a39201063afc270cbb68c9c0c1d3c90937c03f98cfee074605b402e7a30f`). On
  PDF p.39, the sentence just before Lemma 39.20.3 says that the lemma applies
  "for example if τ = fppf, U → M is flat, of finite presentation and
  surjective, and R ≅ U ×_M U". This sentence is not on the tag page.
- `stacks-fppf-covering-021m-2026-11-01`, the tag page of
  [Definition 34.7.1](https://stacks.math.columbia.edu/tag/021M), downloaded
  on 1 November 2026 (directory SHA-256
  `4ccbd8bcf3d37f25e74d72cf78a921c81946155c473096270dcd9b12ddf732a9`): an
  fppf covering of `T` is a family of morphisms `T_i → T` that are flat and
  locally of finite presentation and are jointly surjective.

**The absolute setting.** Stacks works over a base scheme `S`. This module
takes `S = Spec ℤ`. Spec ℤ is terminal among schemes, so every scheme is a
scheme over it in exactly one way, and `U ×_{Spec ℤ} U` is the categorical
product `U × U` of schemes, written `prod.lift t s : R ⟶ U ⨯ U` in Lean. The
definitions below are therefore the Stacks definitions in the case
`S = Spec ℤ`, with every scheme in the universe `u`. A relation over a
general base `S` is a relation in this absolute sense too, because
`U ×_S U → U × U` is a monomorphism. The intended consumers apply the
definitions to presentations of algebraic spaces over an arbitrary base.

## `EtaleEquivalenceRelation`

`Langlands.AlgebraicGeometry.EtaleEquivalenceRelation.{u}` is a structure with
the following fields:

- schemes `U R : Scheme.{u}` and morphisms `t s : R ⟶ U`;
- `mono_lift : Mono (prod.lift t s)`: `j = (t, s) : R ⟶ U ⨯ U` is a
  monomorphism, so for every scheme `T` the `T`-points of `R` are a subset of
  the pairs of `T`-points of `U`;
- `refl`: for every `T : Scheme.{u}` and `a : T ⟶ U` there is `r : T ⟶ R`
  with `r ≫ t = a` and `r ≫ s = a`;
- `symm`: for every `r : T ⟶ R` there is `r' : T ⟶ R` with
  `r' ≫ t = r ≫ s` and `r' ≫ s = r ≫ t`;
- `trans`: for `r r' : T ⟶ R` with `r ≫ s = r' ≫ t` there is `r'' : T ⟶ R`
  with `r'' ≫ t = r ≫ t` and `r'' ≫ s = r' ≫ s`;
- `etale_t : Etale t` and `etale_s : Etale s`, with Mathlib's
  `AlgebraicGeometry.Etale`.

Since `j` is a monomorphism, the three point conditions say that the image of
`R(T)` in `U(T) × U(T)` is an equivalence relation for every scheme `T`. This
is Definition 39.3.1(4) in the form confirmed by comment #6528: a relation that
is a pre-equivalence relation. With `etale_t` and `etale_s` it is
Definition 65.9.2 for `S = Spec ℤ`. The order of the fields `t, s` follows
Stacks' convention `j = (t, s)`. In the statement of Theorem 65.10.5 the pair
is written `(s, t)`, a difference of notation only.

## `EtaleEquivalenceRelation.HasAffineQuotient`

For `E : EtaleEquivalenceRelation.{u}`, `E.HasAffineQuotient : Prop` holds
when there exist `M : Scheme.{u}` and `q : E.U ⟶ M` such that

- `IsAffine M`;
- `IsPullback E.t E.s q q`: `E.t ≫ q = E.s ≫ q`, and this square is a
  pullback, so `(t, s)` identifies `R` with `U ×_M U`;
- `Flat q`, `LocallyOfFinitePresentation q` and `Surjective q`, with Mathlib's
  scheme-morphism properties.

These are the hypotheses of Lemma 39.20.3 in the fppf case noted before it on
PDF p.39, with one difference: that sentence asks for `q` of finite
presentation, and the Lean definition asks only for locally of finite
presentation. The weaker condition is enough for the lemma. By
Definition 34.7.1, the single morphism `q` is an fppf covering of `M`, so
`h_U → h_M` is a surjection of fppf sheaves, which is condition (2) of the
lemma. Condition (1) is the equation `E.t ≫ q = E.s ≫ q`, and condition (3)
holds because `(t, s) : R → U ×_M U` is an isomorphism. By the lemma, `M`
represents the fppf quotient sheaf `U/R`, so `E` has a representable quotient
in the sense of Definition 39.20.2, represented by an affine scheme.
Conversely, Stacks gives the following when `U/R` is represented by an affine
scheme `M`. By Theorem 65.10.5, `U → M` is étale and surjective, hence flat,
locally of finite presentation and surjective. It need not be of finite
presentation, because `U` need not be quasi-compact; this is why the Lean
definition uses the weaker condition. By Lemma 39.20.4, `R → U ×_M U` is
surjective as a map of sheaves; it is injective because `j` is a monomorphism,
so it is an isomorphism. The Lean definition records the explicit data
`(M, q)` instead of a quotient sheaf. Neither direction of this comparison is
proved in Lean here.

## `EtaleEquivalenceRelation.IsCartesianHom`

For `E' E : EtaleEquivalenceRelation.{u}`, `f : E'.U ⟶ E.U` and
`g : E'.R ⟶ E.R`, `IsCartesianHom E' E f g : Prop` is the conjunction of

- `g ≫ E.t = E'.t ≫ f`, and
- `IsPullback g E'.s E.s f`: `g ≫ E.s = E'.s ≫ f`, and the square with top
  `g`, left `E'.s`, right `E.s` and bottom `f` is a pullback.

The two commutativity equations say that `(f, g)` is a morphism of relations:
`j ∘ g = (f × f) ∘ j'`. A morphism of equivalence relations needs no separate
compatibility with composition, because `j` is a monomorphism. The pullback
condition is Definition 39.21.1 for the groupoids attached to the two
relations: the square formed by the morphism on `R`, the source maps `s'` and
`s` and the morphism on `U` is a fibre square. Lemma 39.20.7 then shows that
`E'.U ≅ E.U ×_{U/R} (U'/R')` as fppf sheaves. This consequence is not
formalized here.

## `EtaleEquivalenceRelation.HasFiniteSurjectiveCoverWithAffineQuotient`

For `E : EtaleEquivalenceRelation.{u}`, the proposition
`E.HasFiniteSurjectiveCoverWithAffineQuotient` holds when there exist
`E' : EtaleEquivalenceRelation.{u}`, `f : E'.U ⟶ E.U` and `g : E'.R ⟶ E.R`
with `IsCartesianHom E' E f g`, `IsFinite f`, `Surjective f` and
`E'.HasAffineQuotient`. Here `IsFinite` and `Surjective` are Mathlib's
`AlgebraicGeometry.IsFinite` and `AlgebraicGeometry.Surjective`.

This definition is internal to the planned reduction of Lemma 70.15.1. It is
not a Stacks definition; it is the form that the hypotheses of
Lemma 70.15.1 are meant to take on a presentation. Let
`X = U'/R'` and `Y = U/R`, where `U'`, `R'` belong to `E'`, so that `X` is
an affine scheme. By Lemma 39.20.7, `U' ≅ U ×_Y X` as fppf sheaves, so `f`
is the base change of the induced morphism `X → Y` along the étale
surjection `U → Y`. The planned transfer statement uses this to read `f`
finite and surjective as `X → Y` finite and surjective. That comparison with
the published algebraic-space predicates is not part of this module. The
definition asks for no affineness of `E'.U`: a finite morphism is affine, so
`E'.U` is affine whenever `E.U` is.
