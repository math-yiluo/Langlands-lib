# Statement: maximal tori are conjugate over a finite separable extension

Worker 75.

`Langlands.GroupScheme.MaximalTorusSeparableConjugacyStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no other
definitions, theorems or axioms. It imports:

- [`Torus.Maximal`](Maximal.md), for `IsMaximalTorus` and, through its imports, the
  group-scheme vocabulary: base change `GroupScheme.baseChange`
  ([`AbelianScheme.GroupScheme`](../../AbelianScheme/GroupScheme.md)), inner automorphisms
  `innerIso` ([`InnerAutomorphism`](../InnerAutomorphism.md)) and subgroup functors
  `SubgroupFunctor.range` ([`SubgroupFunctor`](../SubgroupFunctor.md)).
- Mathlib's `Mathlib.FieldTheory.IsSepClosed`, for `IsSepClosed`.

## Lean statement

```lean
def MaximalTorusSeparableConjugacyStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (T T' : CommGroupScheme (Spec (CommRingCat.of k))) (j : T.toGrp ⟶ G)
    (j' : T'.toGrp ⟶ G), IsMaximalTorus j → IsMaximalTorus j' →
      (∃ (K : Type u) (_ : Field K) (_ : Algebra k K) (_ : FiniteDimensional k K)
          (_ : Algebra.IsSeparable k K),
        let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
        ∃ g : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ ((GroupScheme.baseChange b).obj G).X,
          SubgroupFunctor.range ((GroupScheme.baseChange b).map j ≫
              (((GroupScheme.baseChange b).obj G).innerIso g).hom) =
            SubgroupFunctor.range ((GroupScheme.baseChange b).map j')) ∧
      (IsSepClosed k → ∃ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
        SubgroupFunctor.range (j ≫ (G.innerIso g).hom) = SubgroupFunctor.range j')
```

## Objects and predicates used

- **Group schemes.** `GroupScheme S` is `Grp (Over S)` and `CommGroupScheme S` the commutative
  group schemes; `T.toGrp` is the underlying group scheme of `T`. For `G : GroupScheme S`,
  `G.X` is its scheme over `S`, `G.X.left` the underlying scheme and `G.X.hom` the structure
  morphism. A point of `G` over `U : Over S` is a morphism `U ⟶ G.X`; a point over the base
  (a `k`-point when `S = Spec k`) is a morphism `Over.mk (𝟙 S) ⟶ G.X`.
- `Smooth`, `IsAffineHom`, `FiniteDimensional`, `Algebra.IsSeparable`, `IsSepClosed`: as in
  Mathlib.
- `IsMaximalTorus j` ([`Torus.Maximal`](Maximal.md)) for `j : T.toGrp ⟶ G`: `T` is a torus
  (`IsTorus`, Milne's Definition 12.14), `j` is a closed immersion (`IsClosedSubgroup`), and
  whenever `j` factors as `f ≫ j'` through another torus `j' : T'' ⟶ G` that is a closed
  immersion, `f` is an isomorphism. So `T` is a torus of `G` not properly contained in a larger
  torus of `G`.
- `GroupScheme.baseChange b` for `b : Spec K ⟶ Spec k`: the base-change functor from group
  schemes over `Spec k` to group schemes over `Spec K`. Here `b` is `Spec` of `algebraMap k K`,
  so `(GroupScheme.baseChange b).obj G` is `G_K` and `(GroupScheme.baseChange b).map j` is
  `j_K : T_K ⟶ G_K`.
- `G.innerIso g` for a base point `g` ([`InnerAutomorphism`](../InnerAutomorphism.md)): the
  inner automorphism of `G` that sends a point `x` over any `U` to `g x g⁻¹`
  (`InnerAutomorphism.comp_innerIso_hom`).
- `SubgroupFunctor.range i` for `i : H ⟶ G`: the subgroup functor of `G` whose points over `U`
  are the points of `G` over `U` that factor through `i`. Equality of two such ranges means the
  two subgroups have the same points over every scheme `U` over the base, so for closed
  immersions it says that they are the same closed subgroup of `G`.

## Statement and quantifiers

For every field `k : Type u`, every smooth affine group scheme `G` over `Spec k` (not assumed
connected) and all maximal tori `j : T ⟶ G` and `j' : T' ⟶ G`:

1. there are a field `K : Type u` with an algebra structure over `k`, finite and separable over
   `k`, and a `K`-point `g` of `G_K` such that conjugation by `g` carries `T_K` onto `T'_K`:
   `range (j_K ≫ int(g)) = range (j'_K)`, that is, `g T_K g⁻¹ = T'_K` as subgroups of `G_K`;
2. if `k` is separably closed, there is a `k`-point `g` of `G` with `g T g⁻¹ = T'`.

The field `K`, its field and algebra structures and the two instance witnesses are
existentially quantified in part 1, as is `g` in both parts.

## Source

James S. Milne, *Algebraic Groups: The theory of group schemes of finite type over a field*
(Cambridge University Press, 2017), source ID `milne-2017-algebraic-groups`, file
`Milne--Algebraic groups, the theory of group schemes of finite type over a field
(book)--2017.pdf`. Page numbers are printed page numbers; the PDF page is the printed page
plus 16.

- Theorem 17.87, p.380: "Let G be a group variety over a field k, and let T₁ and T₂ be maximal
  tori in G. Then T₁ and T₂ are conjugate by an element of G(k') for some finite separable
  field extension k' of k, i.e., (T₂)_{k'} = g·(T₁)_{k'}·g⁻¹ for some g ∈ G(k')." This is
  part 1.
- The sentence after its proof, p.380: "In particular, any two maximal tori in a group variety G
  over a separably closed field k are conjugate by an element of G(k)." This is part 2.
- Chapter 17 opening, p.352: "Recall also that all algebraic groups are affine over a base
  field k"; remark after 1.26, p.13: a group variety is a smooth algebraic group.
- Section 17d, p.363: "In this section we define a maximal torus in G to be a torus T such
  that T_{k^a} is maximal in G_{k^a}. Later (17.82) we shall see that this agrees with the
  obvious definition."
- Theorem 17.82, p.379: for a group variety `G` over `k` and a field `k'` containing `k`, a
  torus `T` in `G` is maximal if and only if `T_{k'}` is maximal in `G_{k'}`.

The official errata snapshot of 2026-11-02 (source ID
`milne-2017-algebraic-groups-errata-2026-11-02`) lists Chapter 17 corrections only on pp.360,
364 and 386 (the remark before 17.28, Example 17.42 and Exercise 17-7). None concerns
Theorem 17.87 or the sentence after it.

Milne's proof: the functor `R ↦ {g ∈ G(R) | g T₁_R g⁻¹ = T₂_R}` is represented by a closed
subscheme `X` of `G` (1.80). By Theorem 17.10 there is a point `g ∈ X(k^a)`, and `h ↦ gh` is
an isomorphism `N_G(T₁)_{k^a} → X_{k^a}`. Therefore `X` is smooth and nonempty, and so
`X(k') ≠ ∅` for some finite separable field extension `k'` of `k` (A.48). This is explanation
only.

## Derivation from the source

- **Group variety.** A group variety over `k` is a smooth algebraic group, affine by the
  Chapter 17 convention: `[Smooth G.X.hom]` and `[IsAffineHom G.X.hom]` over `Spec k`. Together
  they give finite type over `k`. Theorem 17.87 does not assume `G` connected, and neither does
  the statement.
- **Maximal tori.** On p.363 Milne defines a maximal torus over an arbitrary field as a torus
  `T` in `G` with `T_{k^a}` maximal in `G_{k^a}`, and says that Theorem 17.82 shows this
  "agrees with the obvious definition": a torus of `G` not properly contained in a larger
  torus of `G`. The statement uses the obvious definition, `IsMaximalTorus` over `k`. The
  Library proves the equivalence with maximality after any field extension, for smooth affine
  `G`, as `maximalTorusBaseChange`
  ([`Torus.MaximalBaseChangeProof`](MaximalBaseChangeProof.md)).
- **Finite separable field extension `k'`.** A field `K` with `Algebra k K`,
  `FiniteDimensional k K` and `Algebra.IsSeparable k K`. It lives in the universe `u` of `k`.
- **Conjugate by `g ∈ G(k')`.** `G(k')` is the set of `K`-points of `G_K`, morphisms
  `Over.mk (𝟙 (Spec K)) ⟶ G_K.X`. The equality `(T₂)_{k'} = g·(T₁)_{k'}·g⁻¹` of subgroups of
  `G_{k'}` is read as equality of subgroup functors of `G_K`: the image of `T_K` under
  `j_K ≫ int(g)` has the same points as the image of `T'_K` under `j'_K`, over every scheme
  over `Spec K`. Milne's `T₁, T₂` are `j, j'`.
- **Separably closed case.** `IsSepClosed k`, with `g` a `k`-point of `G`.

## Scope

- The statement does not give the finer information in Milne's proof (the transporter scheme
  and its torsor structure).
- It does not assume that `G` is connected or reductive.

## Related Library results

- `MaximalTorusConjugacyStatement` in
  [`Absolute.BorelStatement`](../Absolute/BorelStatement.md), proved as `maximalTorusConjugacy`
  ([`Absolute.MaximalTorusConjugacyProof`](../Absolute/MaximalTorusConjugacyProof.md)), is
  Milne's Theorem 17.10: over an algebraically closed field, any two maximal tori of a smooth
  connected affine group are conjugate by a `k`-point. It is the input to Milne's proof of
  Theorem 17.87.
- `MaximalTorusBaseChangeStatement`
  ([`Torus.MaximalBaseChangeStatement`](MaximalBaseChangeStatement.md)), proved as
  `maximalTorusBaseChange`, is Milne's Theorem 17.82 for smooth affine `G`.
- `SmoothMaximalSplitTorusConjugacyStatement`
  ([`Rational.MaximalSplitTorusStatement`](../Rational/MaximalSplitTorusStatement.md)) states
  the conjugacy of maximal split tori by `k`-points over any field, a different result.
