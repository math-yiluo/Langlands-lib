# Statement: conjugacy and density of Cartan subgroups

Worker 75.

`Langlands.GroupScheme.CartanConjugacyDensityStatement.{u} : Prop` is a statement-only,
`Prop`-valued definition. This module does not prove it, and it adds no other definitions,
theorems or axioms. It imports:

- [`Cartan.Basic`](Basic.md), for `IsCartanSubgroup` and, through its imports, the
  group-scheme vocabulary over a field.
- [`InnerAutomorphism`](../InnerAutomorphism.md), for the inner automorphism `G.innerIso g`.

## Lean statement

```lean
def CartanConjugacyDensityStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left],
    (∀ (C C' : GroupScheme (Spec (CommRingCat.of k))) (c : C ⟶ G) (c' : C' ⟶ G),
      IsCartanSubgroup c → IsCartanSubgroup c' →
        ∃ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
          SubgroupFunctor.range (c ≫ (G.innerIso g).hom) = SubgroupFunctor.range c') ∧
    ∀ (C : GroupScheme (Spec (CommRingCat.of k))) (c : C ⟶ G), IsCartanSubgroup c →
      ∃ U : Set G.X.left, IsOpen U ∧ Dense U ∧
        U ⊆ Set.range (fst G.X C.X * (snd G.X C.X ≫ c.hom.hom) * (fst G.X C.X)⁻¹).left
```

The module opens `CategoryTheory.MonoidalCategory`, `CategoryTheory.CartesianMonoidalCategory`
and the scoped `CategoryTheory.MonObj` notation, for `⊗`, `fst`, `snd` and the group law on
morphisms into a group object.

## Objects and predicates used

- **Group schemes.** `GroupScheme S` is `Grp (Over S)`. For `G : GroupScheme S`, `G.X` is its
  scheme over `S`; `G.X.left` is the underlying scheme and `G.X.hom` its structure morphism.
  For a homomorphism `c : C ⟶ G`, `c.hom.hom : C.X ⟶ G.X` is the underlying morphism over `S`.
- **`k`-points.** A morphism `g : Over.mk (𝟙 (Spec k)) ⟶ G.X` is a `k`-point of `G`.
- `Smooth`, `IsAffineHom`, `ConnectedSpace`, `IsOpen`, `Dense`, `Set.range`: as in Mathlib.
- `IsCartanSubgroup c` ([`Cartan.Basic`](Basic.md)): `c` is a closed immersion and
  `SubgroupFunctor.range c = torusCentralizer j` for some maximal torus `j : T ⟶ G`. Here
  `IsMaximalTorus j` ([`Torus.Maximal`](../Torus/Maximal.md)) says that `T` is a torus, `j` is a
  closed immersion, and `j` does not factor through a strictly larger closed torus of `G`;
  `torusCentralizer j` ([`Rational.TorusCentralizer`](../Rational/TorusCentralizer.md)) is the
  centralizer `C_G(T)`, tested after every base change.
- `SubgroupFunctor.range f`: the points of `G` that factor through `f`, on every scheme over
  `Spec k`.
- `G.innerIso g` ([`InnerAutomorphism`](../InnerAutomorphism.md)): the inner automorphism
  `x ↦ g x g⁻¹` of `G` for a `k`-point `g`. So `range (c ≫ (G.innerIso g).hom)` is the
  conjugate subgroup `g C g⁻¹`.
- **The conjugation morphism.** With the projections `fst, snd` of `G.X ⊗ C.X` and the
  pointwise group law on morphisms into `G.X`,
  `fst G.X C.X * (snd G.X C.X ≫ c.hom.hom) * (fst G.X C.X)⁻¹ : G.X ⊗ C.X ⟶ G.X`
  is `(g, x) ↦ g c(x) g⁻¹`, and `.left` is its underlying morphism of schemes. It is the same
  morphism as the Library's `BorelPointContainment.conjugation c`
  ([`Absolute.BorelPointContainmentDensity`](../Absolute/BorelPointContainmentDensity.md)),
  written out here to keep the imports small.

## Statement and quantifiers

For every algebraically closed field `k : Type u` and every smooth, affine, connected group
scheme `G` over `Spec k`:

1. for any two Cartan subgroups `c : C ⟶ G` and `c' : C' ⟶ G` there is a `k`-point `g` of `G`
   with `g C g⁻¹ = C'`, as subgroup functors of `G`;
2. for every Cartan subgroup `c : C ⟶ G`, the image of the conjugation morphism
   `G × C ⟶ G`, `(g, x) ↦ g c(x) g⁻¹`, contains a dense open subset `U` of `G`.

**Why (2) is Milne's density assertion.** Milne writes `|X|` for the space of closed points
(p.3) and identifies `|G|` with `G(k)` (p.352). By (1), the Cartan subgroups of `G` are the
conjugates `g C g⁻¹` with `g ∈ G(k)`, so their union is the set of closed points
`g c(x) g⁻¹` with `g ∈ G(k)`, `x ∈ C(k)`. This is the set of closed points of the image `I`
of the conjugation morphism: a closed point of `G` in `I` has a nonempty fibre of finite type
over `k`, hence a `k`-point in its fibre. Open subsets of `G` correspond bijectively to open
subsets of its space of closed points, since `G` is of finite type over a field (Jacobson).

- If `U ⊆ I` is open and dense, its closed points form a dense open subset of `|G|` inside the
  union of the Cartan subgroups.
- Conversely, let `V` be an open subset of `G` whose closed points all lie in the union, with
  `V` meeting every nonempty open subset of `|G|`. Then `V` is dense in `G`, and `V \ I` is
  constructible (Chevalley: `I` is constructible) with no closed point, so it is empty and
  `V ⊆ I`.

`G` is irreducible (smooth and connected over a field), so "nonempty open", as in Theorem
17.33(a), and "dense open", as in Proposition 17.44, are the same condition.

## Source

James S. Milne, *Algebraic Groups: The theory of group schemes of finite type over a field*
(Cambridge University Press, 2017), source ID `milne-2017-algebraic-groups`, file
`Milne--Algebraic groups, the theory of group schemes of finite type over a field
(book)--2017.pdf`. Page numbers are printed page numbers; the PDF page is the printed page
plus 16.

- Proposition 17.44, p.364: "Let G be a connected group variety over k. Every Cartan subgroup
  of G is smooth, connected, and nilpotent. If k is algebraically closed, then any two are
  conjugate by an element of G(k), and the union of the Cartan subgroups of G contains a dense
  open subset of G." Its proof (p.365) uses Theorem 17.33(a): `⋃_{g∈G(k)} g|C|g⁻¹` contains a
  nonempty open subset of `G`.
- Definition 17.43, p.364: "A Cartan subgroup of a connected group variety is the centralizer
  of a maximal torus."
- Section 17d, opening, p.363: the base field need not be algebraically closed there; in this
  statement it is, as in the second sentence of Proposition 17.44.
- Lemma 17.32 and its proof, pp.361-362: the union `⋃ g|H|g⁻¹` is the image of
  `(g, h) ↦ ghg⁻¹`.
- Notation, p.3: "|X| the underlying topological space of closed points"; Chapter 17 opening,
  p.352: over an algebraically closed field `|G|` is identified with `G(k)`, and all algebraic
  groups are affine over the base field; remark after 1.26, p.13: "group variety" means
  "smooth algebraic group".

The official errata snapshot of 2026-11-02 (source ID
`milne-2017-algebraic-groups-errata-2026-11-02`) lists Chapter 17 corrections only on pp.360,
364 and 386. The p.364 entry concerns Example 17.42 ("take I = {1, 2, …, n}"), not
Proposition 17.44.

Milne's proof: two Cartan subgroups `C_G(T)` and `C_G(T')` are conjugate because `T` and `T'`
are (17.10); every conjugate of `C` is a Cartan subgroup, and the conjugates of `C` contain a
nonempty open subset by Theorem 17.33(a). This is explanation only.

## Derivation from the source

- **Connected group variety over an algebraically closed field.** `[IsAlgClosed k]`,
  `[Smooth G.X.hom]`, `[IsAffineHom G.X.hom]`, `[ConnectedSpace G.X.left]`.
- **Cartan subgroups.** Milne's Cartan subgroup `C_G(T)` is a subgroup of `G`; the Library's
  `IsCartanSubgroup c` says that `c` is a closed subgroup with the same points as `C_G(T)`.
  Over an algebraically closed field, maximality of `T` over `k` is Milne's maximality.
- **Conjugacy.** "Conjugate by an element of `G(k)`" is equality of the ranges of
  `c ≫ int(g)` and `c'`, for a `k`-point `g`.
- **Density.** Stated through the image of the conjugation morphism of one Cartan subgroup,
  which by (1) and the argument above is equivalent to Milne's assertion about the union of all
  Cartan subgroups.
- **The first sentence of Proposition 17.44** (smooth, connected, nilpotent, over any field) is
  already the Library statement [`Cartan.StructureStatement`](StructureStatement.md), proved in
  [`Cartan.StructureProof`](StructureProof.md); it is not repeated here.

## Related Library results

- [`Cartan.StructureStatement`](StructureStatement.md): every Cartan subgroup of a smooth
  connected affine group over a field is smooth, connected and nilpotent.
- [`Torus.CentralizerConnected`](../Torus/CentralizerConnected.md) proves that the centralizer
  of a torus is connected (Milne 17.38), so Milne's `C_G(T)°` in Theorem 17.33(a) is the
  Cartan subgroup `C_G(T)` itself.
