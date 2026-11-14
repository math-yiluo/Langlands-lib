# Statement: connected groups act trivially on central extensions of multiplicative type

Worker 75.

`Langlands.GroupScheme.MultiplicativeTypeExtensionActionStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It imports:

- [`Torus.MultiplicativeType`](MultiplicativeType.md), for the field-level predicate
  `IsMultiplicativeType` and, through its imports, `IsClosedSubgroup` and
  `SubgroupFunctor.range`;
- [`AutomorphicAction`](../AutomorphicAction.md), for actions of one group scheme on another
  by group automorphisms;
- [`Rational.Characters`](../Rational/Characters.md), for the centre `center H` and the
  predicate `IsCentral`;
- [`Rational.RootSubgroupStructureStatement`](../Rational/RootSubgroupStructureStatement.md),
  for the fppf quotient predicate `RelativeRoot.IsFppfQuotient`.

`GroupScheme S` is `Grp (Over S)`, and a morphism `j : N ⟶ H` in it is a homomorphism of
group schemes over `S`. Its underlying morphism of `S`-schemes is `j.hom.hom : N.X ⟶ H.X`,
and `G.X.left` is the underlying scheme of `G`. A point of `H` over a test object
`T : Over S` is a morphism `T ⟶ H.X` over `S`.

## Lean statement

```lean
def MultiplicativeTypeExtensionActionStatement : Prop :=
  ∀ (k : Type u) [Field k] (G H N Q : GroupScheme (Spec (CommRingCat.of k)))
    (j : N ⟶ H) (p : H ⟶ Q),
    LocallyOfFiniteType G.X.hom → QuasiCompact G.X.hom → ConnectedSpace G.X.left →
    LocallyOfFiniteType H.X.hom → QuasiCompact H.X.hom →
    IsClosedSubgroup j → IsCentral j → RelativeRoot.IsFppfQuotient (SubgroupFunctor.range j) p →
    IsMultiplicativeType N → IsMultiplicativeType Q →
      ∀ a : AutomorphicAction G H,
        (∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X) (x : T ⟶ H.X),
          x ∈ (SubgroupFunctor.range j).carrier T →
            a.act g x ∈ (SubgroupFunctor.range j).carrier T) →
        ∀ (T : Over (Spec (CommRingCat.of k))) (g : T ⟶ G.X) (x : T ⟶ H.X), a.act g x = x
```

## Predicates used

- `IsMultiplicativeType N` (field level): there are a field `K : Type u`, an algebra
  `k → K`, a finitely generated abelian group `Λ : Type u` and an isomorphism of group
  schemes over `Spec K` from the base change `N_K` onto
  `Diagonalizable.groupScheme (CommRingCat.of K) Λ`, the diagonalizable group
  `D_K(Λ) = Spec K[Λ]`. This is Milne's Definition 12.17 for algebraic groups (groups of
  finite type), as documented in [`Torus.MultiplicativeType`](MultiplicativeType.md).
- `IsClosedSubgroup j`: the underlying morphism of schemes `j.hom.hom.left` is a closed
  immersion.
- `center H`: the subgroup functor of `H` whose `T`-points are the points `h : T ⟶ H.X`
  such that for every `b : T' ⟶ T`, the restriction `b ≫ h` commutes with every point of
  `H` over `T'`. `IsCentral j` says that for every `T` and every `x : T ⟶ N.X`, the point
  `x ≫ j.hom.hom` lies in `center H` over `T`.
- `SubgroupFunctor.range j`: the subgroup functor of `H` whose `T`-points are the
  `T`-points of `H` that factor through `j`. Its set of `T`-points is
  `(SubgroupFunctor.range j).carrier T`.
- `RelativeRoot.IsFppfQuotient (SubgroupFunctor.range j) p` for `p : H ⟶ Q`: the morphism
  `p.hom.hom.left` is flat, surjective and locally of finite presentation, and the subgroup
  functor of points of the scheme-theoretic kernel `kernel p` is exactly
  `SubgroupFunctor.range j`.
- `AutomorphicAction G H`: a morphism `a.hom : G.X ⊗ H.X ⟶ H.X` of schemes over `Spec k`
  such that, on the points over every test object `T`, the identity of `G` acts trivially,
  `(g g') · x = g · (g' · x)`, and `g · (x x') = (g · x) (g · x')`. So it is an action of
  `G` on `H` in which each point of `G` acts by a group homomorphism.
  `a.act g x : T ⟶ H.X` is the action `g · x` of a point `g : T ⟶ G.X` on a point
  `x : T ⟶ H.X`, that is, the composite of the pair `(g, x)` with `a.hom`.

## Statement and quantifiers

The proposition quantifies over a field `k : Type u`, group schemes `G`, `H`, `N`, `Q`
over `Spec k`, and homomorphisms `j : N ⟶ H` and `p : H ⟶ Q`, under these hypotheses:

- the structure morphisms of `G` and `H` are locally of finite type and quasi-compact, and
  the underlying space of `G` is connected;
- `j` is a closed immersion, and it is central;
- `p` is flat, surjective and locally of finite presentation, with kernel `range j`;
- `N` and `Q` are of multiplicative type.

The conclusion: let `a` be an action of `G` on `H` by group automorphisms that preserves
`N`. That is, for every test object `T`, every point `g : T ⟶ G.X` and every point
`x : T ⟶ H.X` that factors through `j`, the point `a.act g x` also factors through `j`.
Then for every test object `T` and all points `g : T ⟶ G.X` and `x : T ⟶ H.X`, the point
`a.act g x` equals `x`. So the action is trivial.

The groups `G` and `H` are not assumed to be affine, smooth or reduced, and `H` is not
assumed to be connected or commutative. Milne's Corollary 12.41 is stated under his
convention that algebraic groups are affine. Dropping affineness of `G` makes this statement
a derived generalization of the corollary as printed; dropping it for `H` excludes nothing.
Both points are explained under "Affineness" in the Derivation section below.

## Source

James S. Milne, *Algebraic Groups: The theory of group schemes of finite type over a field*
(Cambridge University Press, 2017), source ID `milne-2017-algebraic-groups`, file
`Milne--Algebraic groups, the theory of group schemes of finite type over a field
(book)--2017.pdf`. Page numbers are printed page numbers; the PDF page is the printed page
plus 16.

- Corollary 12.41, p.244: "Let N be a normal subgroup of an algebraic group H such that N
  and H/N are of multiplicative type. Every action of a connected algebraic group G on H
  by group homomorphisms preserving N is trivial."
- Milne's proof: "Corollary 12.37 shows that the action of G on H factors through an
  action G × H/N → H, and then through an action G × H/N → N. Theorem 12.36 now shows
  that this action is trivial." This is explanation only.
- Convention on affineness, p.162 (end of Chapter 8): "We now concentrate on affine
  algebraic groups. By “algebraic group” we shall mean “affine algebraic group” and by
  “group variety” we shall mean “affine group variety”." The opening of Chapter 12, p.230,
  repeats: "Recall that all algebraic groups are affine over a base field k." So in
  Corollary 12.41 as printed, `G` and `H` are affine.
- Theorem 12.36, p.243: for diagonalizable groups `G` and `H` over `k` and a connected
  algebraic scheme `X` over `k`, a morphism `X × G → H` that is a homomorphism in the second
  variable takes the same values at every point of `X` as at a fixed point `x₀ ∈ X(k)`. Here
  `X` is any connected algebraic scheme; it need not be affine or a group.
- Summary 1.36, p.17 (Chapter 1, where algebraic groups are not yet assumed affine): an
  algebraic group is connected if and only if it is geometrically connected.

J. S. Milne, *Errata for Algebraic Groups (2017)*, official author page, HTML snapshot of
2026-11-02, source ID `milne-2017-algebraic-groups-errata-2026-11-02`, file
`J. S. Milne - Errata for Algebraic Groups (2017), HTML snapshot 2026-11-02.html`
(SHA-256 `a0c3a10dc376e1c9bd1de05b33beaf7d54e5f1ea7b408d594cfd70231a7ba0cf`).

- Chapter 12: "p.244. In 12.41, N should be a central subgroup of H. This suffices for the
  applications."

The statement follows the corrected version: `N` is a central subgroup of `H`. Milne uses
12.41 several times, for example in the proofs of Corollary 12.42 (p.244), Lemma 16.43
(p.340), Corollary 17.62(e) (p.373) and Proposition 18.2 (p.387); the errata state that the
central version suffices for the applications. For instance, Corollary 12.42 applies 12.41
to the conjugation action of a connected extension `G` on itself. There `N` is a normal
subgroup of multiplicative type of a connected group, hence central by Corollary 12.38
(p.244).

A sketch of why the central hypothesis suffices: by 12.37 the group `G` acts trivially on
`N` and on `H/N`, so `g · h = h · c(g, h)` with `c(g, h)` in `N`. Because `N` is central,
`h ↦ c(g, h)` is a homomorphism `H → N` that is trivial on `N`. So it comes from a family
of homomorphisms `H/N → N` parametrized by `G`, which is constant by Theorem 12.36 (after
extending scalars until `N` and `H/N` are diagonalizable). Its value at the identity of
`G` is trivial. This is explanation only.

## Derivation from the source

- **Algebraic group.** Milne's algebraic groups are group objects in the category of
  algebraic schemes over `k`, that is, schemes of finite type over `k` (Definition 1.1,
  p.6). The statement encodes "`G` is of finite type over `k`" as
  `LocallyOfFiniteType G.X.hom` together with `QuasiCompact G.X.hom`, and the same for
  `H`. "Connected" is `ConnectedSpace G.X.left`; this includes nonemptiness, which holds
  for every group scheme.
- **Affineness.** From p.162 on, and so in Chapter 12, Milne's algebraic groups are affine
  (see Source). The statement does not assume this.
  - *Acting group `G` (derived generalization).* The statement allows any connected group
    `G` of finite type over `k`, affine or not, so it is more general than Corollary 12.41
    as printed. The source argument does not use affineness of `G`. In Milne's proof, `G`
    enters only as the parameter scheme in Theorem 12.36 (directly, and through Corollary
    12.37 for the induced actions on `N` and on `H/N`). Theorem 12.36 allows any connected
    algebraic scheme as parameter space, with a `k`-point; here the point is the identity of
    `G`. To make `N` and `H/N` diagonalizable one extends scalars to a field `K`. The group
    `G_K` is still connected, because a connected algebraic group is geometrically connected
    (Summary 1.36, p.17, proved before the affine convention is introduced). Equality of the
    two morphisms `G × H → H` given by `(g, h) ↦ g · h` and `(g, h) ↦ h` can be checked
    after such a field extension. This is explanation only; the module proves nothing.
  - *Group `H` (nothing excluded).* Groups of multiplicative type are affine (Definition
    12.17 and `D(M) = Spec k[M]`), so `N` and `Q` are affine. The map `p : H → Q` is
    faithfully flat with kernel `N`, so `H ×_Q H ≅ H × N` and `p` is an `N`-torsor. Hence `p`
    is an affine morphism (affineness descends along the fppf cover `p`), and `H` is affine
    because `Q` is. So the hypotheses already force `H` to be affine. This too is
    explanation only.
- **Central subgroup.** In Milne a subgroup of an algebraic group is an algebraic subgroup,
  that is, a closed group subscheme. The statement takes a homomorphism `j : N ⟶ H` that
  is a closed immersion (`IsClosedSubgroup j`). "Central" is `IsCentral j`: every point of
  `N` maps to a point of the centre `center H`, whose points over `T` are those that
  commute with every point of `H` over every `T' → T`. A central subgroup is normal, so
  the quotient `H/N` exists as an algebraic group.
- **The quotient `H/N`.** The quotient map `H → H/N` of algebraic groups is faithfully
  flat with kernel `N` (Milne, Definition 5.5, p.99, and Theorem 5.14, p.102). The statement
  takes a homomorphism `p : H ⟶ Q` with `RelativeRoot.IsFppfQuotient
  (SubgroupFunctor.range j) p`: `p` is flat, surjective and locally of finite presentation,
  and its kernel has the same points as `N`. This is the encoding of short exact sequences
  used in [`Torus.CentralExtensionStatement`](CentralExtensionStatement.md).
  Over a field such a `p` is a quotient map in Milne's sense, so `Q` is `H/N`.
- **Multiplicative type.** "N and H/N are of multiplicative type" is
  `IsMultiplicativeType N` and `IsMultiplicativeType Q`, the Library's form of Milne's
  Definition 12.17 (p.236).
- **Action by group homomorphisms preserving N.** Milne's action `G × H → H` is a morphism
  of schemes that is an action on `R`-points for every `k`-algebra `R`, with each map
  `h ↦ g · h` a homomorphism `H(R) → H(R)`. `AutomorphicAction G H` encodes the same data
  as one morphism of schemes `G.X ⊗ H.X ⟶ H.X` with the three laws tested on points over
  every scheme `T` over `Spec k`. "Preserving N" means that `g · n` lies in `N(R)` for
  all `g ∈ G(R)` and `n ∈ N(R)`. The statement asks this on points over every test scheme
  `T`, where the points of `N` are the points of `H` that factor through `j`.
- **Trivial.** "The action is trivial" means `g · h = h` for all `R` and all
  `(g, h) ∈ G(R) × H(R)`. The statement asserts `a.act g x = x` on points over every test
  scheme `T`.
- **Universes.** The field `k`, the splitting fields and the character groups in
  `IsMultiplicativeType` all live in the universe `u`.

## Related Library results

- [`Torus.CentralExtensionStatement`](CentralExtensionStatement.md) states that a central
  extension of a torus by a torus over a field is a torus. Its docstring cites Milne 12.41
  and 12.22 as the route; its conclusion is different.
- [`Torus.HomFamilyRigidity`](HomFamilyRigidity.md) proves the rigidity of families of
  homomorphisms between split tori parametrized by a connected scheme over any base, the
  split-torus case of Milne's Theorem 12.36.
- [`Rational.AlgClosedNormalSolvableTorusStatement`](../Rational/AlgClosedNormalSolvableTorusStatement.md)
  cites Milne's Corollaries 12.37 and 12.38, the rigidity results behind the present
  statement, in its proof outline.
