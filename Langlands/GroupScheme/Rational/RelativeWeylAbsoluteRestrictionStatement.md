# The relative Weyl group as restrictions of absolute Weyl elements: statement

Worker 3483.

`Langlands.GroupScheme.RelativeWeylAbsoluteRestrictionStatement.{u}` is a
proposition definition. This module does not prove it.

## The statement

Let `k` and `K` be fields in the universe `u`, with a `k`-algebra structure on
`K`, and write `b = algebraBaseMap k K : Spec K ⟶ Spec k`. Let `G` be a group
scheme over `Spec k` with `IsConnectedReductive G`. Let `S` be a commutative
group scheme over `Spec k` and `i : S.toGrp ⟶ G` a maximal split torus,
`IsMaximalSplitTorus i`.

Write `G_K = (GroupScheme.baseChange b).obj G`,
`S_K = (CommGroupScheme.baseChange b).obj S` and
`i_K = (GroupScheme.baseChange b).map i` for the actual base changes. Let `T`
be a commutative group scheme over `Spec K` and `j : T.toGrp ⟶ G_K` a maximal
split torus of `G_K` over `K`, `IsMaximalSplitTorus j`. Let `f : S_K ⟶ T` be a
homomorphism with `CommGroupScheme.groupHom f ≫ j = i_K`; so `T` contains
`S_K` as a subgroup of `G_K`.

A rational point `n` of a group scheme normalizes `i` through an automorphism
`σ` when `IsNormalizingPoint i n σ`, that is, `i ≫ int(n) = σ ≫ i`.
`normalizerPoints i` and `centralizerPoints i` are the subgroups of rational
points that normalize `i` through some automorphism and through the identity,
respectively. Points of `G_K` are multiplied in the group of rational points
(`open scoped CategoryTheory.MonObj`).

The statement asserts the conjunction of three properties.

1. **Factorization of the normalizer.** For every rational point `n` of `G_K`
   in `normalizerPoints i_K`, there are a rational point `m` in
   `normalizerPoints i_K ⊓ normalizerPoints j` and a rational point `z` in
   `centralizerPoints i_K` with `n = m * z`.
2. **Equality of the induced automorphism groups.** The set of automorphisms
   `τ : S_K ≅ S_K` of the form `(CommGroupScheme.baseChange b).mapIso σ`, where
   `σ : S ≅ S` satisfies `IsNormalizingPoint i n σ` for some rational point
   `n` of `G`, equals the set of `τ` with `IsNormalizingPoint i_K m τ` for some
   rational point `m` of `G_K` in `normalizerPoints j`.
3. **Injectivity of base change on the induced automorphisms.** If a rational
   point `n` of `G` satisfies `IsNormalizingPoint i n σ` and
   `(CommGroupScheme.baseChange b).mapIso σ = Iso.refl _`, then `n` is in
   `centralizerPoints i`.

All normalizing equations are equalities of group-scheme morphisms, so they
hold on every test scheme. The field `K` is an arbitrary extension of `k`; it
need not be algebraic.

## Source

Armand Borel and Jacques Tits, *Groupes réductifs*, Publ. Math. IHÉS 27
(1965), source ID `borel-tits-1965-groupes-reductifs`, Corollaire 5.5,
printed p.97 (PDF p.44):

> 5.5. Corollaire. — Soient K une extension de k, T un tore déployé sur K
> maximal de G contenant S. Soient 𝒩(S, T) = 𝒩(S) ∩ 𝒩(T) et
> _K W_k = 𝒩(S, T)/𝒵(T). Alors 𝒩(S) = 𝒩(S, T).𝒵(S), et _k W s'identifie à
> la restriction de _K W_k à S.
>
> Pour démontrer la première égalité, il suffit, vu le théorème, de faire voir
> que 𝒩(S)_k ⊂ 𝒩(S, T).𝒵(S), ce qui résulte de 4.22. La deuxième assertion
> n'est qu'une autre manière d'énoncer la première.

Here `G` is a connected reductive `k`-group and `S` a maximal `k`-split torus,
by the standing hypothesis of §5 (printed p.95, PDF p.42): "Dans tout ce
paragraphe, G est réductif connexe, et S est un tore déployé sur k maximal de
G." `𝒩` and `𝒵` denote normalizers and centralizers, and 5.1 (same page)
defines `_k W = 𝒩(S)/𝒵(S)`. "Le théorème" is Théorème 5.3, printed
pp.96–97 (PDF pp.43–44), whose last assertion is "Chaque composante connexe de
𝒩(S) rencontre G_k". The proof uses Corollaire 4.22, printed p.93 (PDF p.40):

> 4.22. Corollaire. — Soient S, S' des tores déployés sur k maximaux de G et
> A, A' des parties de S_k et S'_k ou des sous-tores de S et S'
> respectivement. Soit x ∈ G_k tel que ^x A = A'. Alors il existe y ∈ G_k tel
> que ^y S = S' et ^y a = ^x a (a ∈ A).

The 1972 *Compléments* (source ID
`borel-tits-1972-complements-groupes-reductifs`, §5, printed pp.274–275)
list corrections to the 1965 article. None changes 4.22, 5.3 or 5.5. Their
only entry for printed p.97 replaces a bibliographic reference in the proof of
5.3 (to Bourbaki, chap. V, 3.3, Prop. 1).

## Correspondence with the source

Borel and Tits work with algebraic groups identified with their points over a
universal domain. The Lean statement is a statement about rational points, in
the language of the Library.

- **Hypotheses.** "T un tore déployé sur K maximal de G contenant S" is a
  maximal `K`-split torus `j : T ⟶ G_K` (`IsMaximalSplitTorus` over `K`)
  through which `i_K` factors (`groupHom f ≫ j = i_K`). "Tore déployé sur k
  maximal" is Borel–Tits' term for a maximal `k`-split torus (4.21: "Les tores
  déployés sur k maximaux de G sont conjugués sur k"). The family-5 ledger
  paraphrases `T` as a maximal torus split over `K`; that is the case where
  `G_K` is split. The torus `S`, the group `G` and the extension `K` are as in
  the source.
- **Conjunct 1** is the first equality `𝒩(S) = 𝒩(S, T).𝒵(S)` in its form for
  `K`-points: every `K`-point normalizing `S_K` is the product of a `K`-point
  of `𝒩(S, T) = 𝒩(S) ∩ 𝒩(T)` and a `K`-point of `𝒵(S)`. This is what the
  source's argument gives. Apply 4.22 over `K` to the connected reductive
  group `G_K`, with `S = S' = T`, `A = A' = S_K` and `x = n`; it gives a
  `K`-point `y` normalizing `T` that acts on `S_K` as `n` does, so `m = y` and
  `z = y⁻¹ n`. Borel–Tits apply 4.22 only to `x ∈ 𝒩(S)_k` and combine it with
  Théorème 5.3; the same application of 4.22 works for every `K`-point of
  `𝒩(S)`. When `K` is algebraically closed, conjunct 1 is the source's
  equality on geometric points. The Lean statement does not assert that
  equality for a non-closed `K`, nor any equality of group schemes.
- **Conjunct 2** is the identification of `_k W` with the restriction of
  `_K W_k` to `S`, as subgroups of the automorphisms of `S_K`. The
  automorphisms of `S` induced by `k`-points of `𝒩(S)`, base changed to `K`,
  represent `_k W`. By Théorème 5.3 every element of `_k W` is represented by
  a `k`-point, since every connected component of `𝒩(S)` meets `G_k`. The restriction of `_K W_k = 𝒩(S, T)/𝒵(T)` to `S` is the
  group of automorphisms of `S` induced by elements of `𝒩(S, T)`. The Lean
  statement uses the `K`-points of `G_K` normalizing `T` and `S_K`. These
  give all such automorphisms: by Théorème 5.3 over `K`, every element of
  `𝒩(T)` is a `K`-point of `𝒩(T)` times an element of the identity
  component `𝒩(T)⁰ = 𝒵(T)⁰`. The `K`-point then acts on `T`, hence on `S_K`,
  as the given element does.
- **Conjunct 3** is the injectivity half of "s'identifie". The map from
  `_k W = 𝒩(S)_k/𝒵(S)_k` to automorphisms of `S_K` has kernel `𝒵(S)_k`: a
  `k`-point whose induced automorphism of `S` becomes the identity after base
  change to `K` centralizes `S`.

Conjuncts 2 and 3 together say that `_k W`, acting on `S` and base changed
to `K`, is isomorphic to the restriction of `_K W_k` to `S_K`. The statement
does not construct `_K W_k` as a quotient group, nor a homomorphism between
the two Weyl groups.

## Relation to other Library statements

- `SplitMaximalTorusWeylRationalityStatement`
  (`Reductive/SplitWeylRationalityStatement`) is the case of a split maximal
  torus. When `S` is a maximal torus, `S_K` is a maximal torus of `G_K`, so
  `f` is an isomorphism, `𝒩(S, T) = 𝒩(S)` and `𝒵(S) = S`. Its assertion then
  corresponds to the inclusion `⊇` of conjunct 2. The
  present statement covers a maximal split torus of any connected reductive
  `G`, compared with a maximal split torus over an arbitrary extension.
- `RelativeWeylGroupRestrictStatement` (`Rational/TorusNormalizerStatement`)
  compares `normalizerPoints i / centralizerPoints i` with the corresponding
  quotient for `U`-points of `G` over a connected `k`-scheme `U`. It concerns
  the same torus `S` and does not involve a torus `T` of `G_K`.

This is row I2 of the published family-5 ledger
(`notes/group-schemes/ledger-family-5-rational.md`), which records that no
Lean statement of Borel–Tits 5.5 existed.
