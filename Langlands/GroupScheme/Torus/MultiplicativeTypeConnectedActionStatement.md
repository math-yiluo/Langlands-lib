# Statement: connected groups act trivially on groups of multiplicative type

Worker 75.

`Langlands.GroupScheme.MultiplicativeTypeConnectedActionStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no
other definitions, theorems or axioms. It imports:

- [`Torus.MultiplicativeType`](MultiplicativeType.md), for the field-level predicate
  `IsMultiplicativeType` and, through its imports, `IsClosedSubgroup` and
  `SubgroupFunctor.range`;
- [`AutomorphicAction`](../AutomorphicAction.md), for actions of one group scheme on another
  by group automorphisms;
- [`Rational.Characters`](../Rational/Characters.md), for the centre `center G` and the
  predicate `IsCentral`.

`GroupScheme S` is `Grp (Over S)`, and a morphism `h : H ⟶ G` in it is a homomorphism of
group schemes over `S`. Its underlying morphism of `S`-schemes is `h.hom.hom : H.X ⟶ G.X`,
and `G.X.left` is the underlying scheme of `G`. A point of `G` over a test object
`T : Over S` is a morphism `T ⟶ G.X` over `S`.

## Lean statement

```lean
def MultiplicativeTypeConnectedActionStatement : Prop :=
  ∀ (k : Type u) [Field k] (G H : GroupScheme (Spec (CommRingCat.of k))),
    LocallyOfFiniteType G.X.hom → QuasiCompact G.X.hom → ConnectedSpace G.X.left →
    IsMultiplicativeType H →
      (∀ (a : AutomorphicAction G H) (T : Over (Spec (CommRingCat.of k)))
          (g : T ⟶ G.X) (x : T ⟶ H.X), a.act g x = x) ∧
      (∀ h : H ⟶ G, IsClosedSubgroup h → (SubgroupFunctor.range h).IsNormal → IsCentral h)
```

## Predicates used

- `IsMultiplicativeType H` (field level): there are a field `K : Type u`, an algebra
  `k → K`, a finitely generated abelian group `Λ : Type u` and an isomorphism of group
  schemes over `Spec K` from the base change `H_K` onto
  `Diagonalizable.groupScheme (CommRingCat.of K) Λ`, the diagonalizable group
  `D_K(Λ) = Spec K[Λ]`. This is Milne's Definition 12.17 for algebraic groups (groups of
  finite type), as documented in [`Torus.MultiplicativeType`](MultiplicativeType.md).
- `AutomorphicAction G H`: a morphism `a.hom : G.X ⊗ H.X ⟶ H.X` of schemes over `Spec k`
  such that, on the points over every test object `T`, the identity of `G` acts trivially,
  `(g g') · x = g · (g' · x)`, and `g · (x x') = (g · x) (g · x')`. So it is an action of
  `G` on `H` in which each point of `G` acts by a group homomorphism.
  `a.act g x : T ⟶ H.X` is the action `g · x` of a point `g : T ⟶ G.X` on a point
  `x : T ⟶ H.X`, that is, the composite of the pair `(g, x)` with `a.hom`.
- `IsClosedSubgroup h`: the underlying morphism of schemes `h.hom.hom.left` is a closed
  immersion.
- `SubgroupFunctor.range h`: the subgroup functor of `G` whose `T`-points are the
  `T`-points of `G` that factor through `h`. `F.IsNormal` says that for every test object
  `T`, the `T`-points of `F` are stable under conjugation by all `T`-points of `G`.
- `center G`: the subgroup functor of `G` whose `T`-points are the points `g : T ⟶ G.X`
  such that for every `a : T' ⟶ T`, the restriction `a ≫ g` commutes with every point of
  `G` over `T'`. `IsCentral h` says that for every `T` and every `x : T ⟶ H.X`, the point
  `x ≫ h.hom.hom` lies in `center G` over `T`.

## Statement and quantifiers

The proposition quantifies over a field `k : Type u` and group schemes `G`, `H` over
`Spec k` such that the structure morphism of `G` is locally of finite type and
quasi-compact, the underlying space of `G` is connected, and `H` is of multiplicative type.
Its conclusion is the conjunction of two parts.

1. For every action `a` of `G` on `H` by group automorphisms, every test object `T` and all
   points `g : T ⟶ G.X` and `x : T ⟶ H.X`, the point `a.act g x` equals `x`. So every
   action of `G` on `H` by group homomorphisms is trivial.
2. For every homomorphism `h : H ⟶ G` that is a closed immersion and whose range is a
   normal subgroup functor of `G`, the homomorphism `h` is central.

The group `G` is not assumed to be affine, smooth or reduced, and `H` is not assumed to be
connected or smooth. Milne's Corollaries 12.37 and 12.38 are stated under his convention
that algebraic groups are affine. Dropping affineness of `G` makes this statement a derived
generalization of the corollaries as printed; `H` is affine anyway. Both points are
explained under "Affineness" in the Derivation section below.

## Source

James S. Milne, *Algebraic Groups: The theory of group schemes of finite type over a field*
(Cambridge University Press, 2017), source ID `milne-2017-algebraic-groups`, file
`Milne--Algebraic groups, the theory of group schemes of finite type over a field
(book)--2017.pdf`. Page numbers are printed page numbers; the PDF page is the printed page
plus 16.

- Corollary 12.37, p.244: "Every action μ: G × H → H by group homomorphisms of a connected
  algebraic group G on a group H of multiplicative type is trivial." This is part 1.
- Corollary 12.38, p.244: "Every normal multiplicative subgroup N of a connected algebraic
  group G is contained in the centre of G." This is part 2.
- Milne proves 12.37 from the rigidity theorem, Theorem 12.36, p.243: a family of
  homomorphisms between diagonalizable groups parametrized by a connected algebraic scheme
  is constant. He proves 12.38 by applying 12.37 to the action of `G` on `N` by inner
  automorphisms. This is explanation only.
- Remark 12.39(b), p.244, shows that the hypothesis "by group homomorphisms" is needed: the
  multiplication of `G_m` is a nontrivial action of `G_m` on the scheme `G_m`.
- Convention on affineness, p.162 (end of Chapter 8): "We now concentrate on affine
  algebraic groups. By “algebraic group” we shall mean “affine algebraic group” and by
  “group variety” we shall mean “affine group variety”." The opening of Chapter 12, p.230,
  repeats: "Recall that all algebraic groups are affine over a base field k." So in
  Corollaries 12.37 and 12.38 as printed, `G` is affine.
- Theorem 12.36, p.243: for diagonalizable groups `G` and `H` over `k` and a connected
  algebraic scheme `X` over `k`, a morphism `X × G → H` that is a homomorphism in the second
  variable takes the same values at every point of `X` as at a fixed point `x₀ ∈ X(k)`. Here
  `X` is any connected algebraic scheme; it need not be affine or a group.
- Summary 1.36, p.17 (Chapter 1, where algebraic groups are not yet assumed affine): an
  algebraic group is connected if and only if it is geometrically connected.

## Derivation from the source

- **Algebraic group.** Milne's algebraic groups are group objects in the category of
  algebraic schemes over `k`, that is, schemes of finite type over `k` (Definition 1.1,
  p.6). The statement encodes "`G` is of finite type over `k`" as
  `LocallyOfFiniteType G.X.hom` together with `QuasiCompact G.X.hom`. "Connected" is
  `ConnectedSpace G.X.left`; this includes nonemptiness, which holds for every group
  scheme.
- **Affineness.** From p.162 on, and so in Chapter 12, Milne's algebraic groups are affine
  (see Source). The statement does not assume that `G` is affine, so it is a derived
  generalization of Corollaries 12.37 and 12.38 as printed. The source argument does not
  use affineness of `G`: in the proof of 12.37, `G` enters only as the parameter scheme of
  Theorem 12.36, applied to `(g, h) ↦ g · h`, and 12.36 allows any connected algebraic scheme
  with a `k`-point as parameter space; here the point is the identity of `G`. To make `H`
  diagonalizable one extends scalars to a field `K`. The group `G_K` is still connected,
  because a connected algebraic group is geometrically connected (Summary 1.36, p.17, proved
  before the affine convention is introduced), and equality of the two morphisms
  `G × H → H` given by `(g, h) ↦ g · h` and `(g, h) ↦ h` can be checked after such a field
  extension. Corollary 12.38 is 12.37 applied to the action of `G` on `N` by inner
  automorphisms, so it generalizes in the same way. A group of multiplicative type is
  affine (Definition 12.17 and `D(M) = Spec k[M]`), so not assuming `H` affine excludes
  nothing. This is explanation only; the module proves nothing.
- **Group of multiplicative type.** Milne's `H` is an algebraic group of multiplicative
  type in the sense of Definition 12.17, p.236. This is the Library's
  `IsMultiplicativeType H`.
- **Action by group homomorphisms.** Milne's action `μ : G × H → H` is a morphism of
  schemes that is an action on `R`-points for every `k`-algebra `R`, with each
  `h ↦ μ(g, h)` a homomorphism `H(R) → H(R)`. `AutomorphicAction G H` encodes the same
  data as one morphism of schemes `G.X ⊗ H.X ⟶ H.X` with the three laws tested on points
  over every scheme `T` over `Spec k`. Each point of `G` then acts by an automorphism,
  with inverse the action of its inverse. "Trivial" means `μ(g, h) = h` for all `R` and
  all `(g, h) ∈ G(R) × H(R)`, as in the last line of Milne's proof; the statement asserts
  this on points over every test scheme `T`.
- **Normal multiplicative subgroup.** In Milne a subgroup of an algebraic group is an
  algebraic subgroup, that is, a closed group subscheme; it is normal when `N(R)` is normal
  in `G(R)` for every `k`-algebra `R` (Definition 1.51, p.21). The statement takes a
  homomorphism `h : H ⟶ G` that is a closed immersion (`IsClosedSubgroup h`), with `H` of
  multiplicative type, and asks the subgroup functor `SubgroupFunctor.range h` of its
  points to be normal on every test scheme. For a closed subgroup, normality on all
  affine test schemes is equivalent to normality on all test schemes.
- **Contained in the centre.** "N is contained in the centre of G" is `IsCentral h`: every
  point of `H` maps to a point of the centre `center G`, whose points over `T` are those
  that commute with every point of `G` over every `T' → T`.
- **Universes.** The field `k`, the splitting field and the character group in
  `IsMultiplicativeType` all live in the universe `u`.

## Related Library results

- [`Torus.HomFamilyRigidity`](HomFamilyRigidity.md) proves the rigidity of families of
  homomorphisms between split tori parametrized by a connected scheme over any base, the
  split-torus case of Milne's Theorem 12.36. It does not cover diagonalizable groups with
  torsion or nonsplit groups of multiplicative type.
- [`Rational.AlgClosedNormalSolvableTorusStatement`](../Rational/AlgClosedNormalSolvableTorusStatement.md)
  cites Corollaries 12.37 and 12.38 in its proof outline but does not state them.
- `IsSolvableGroupScheme.isCentral_of_normal_of_isConnectedReductive`
  ([`Absolute.NormalSolvableCentrality`](../Absolute/NormalSolvableCentrality.md)) proves
  centrality of smooth, connected, affine, solvable, normal closed subgroups of connected
  reductive groups over algebraically closed fields. Its hypotheses differ from part 2.
