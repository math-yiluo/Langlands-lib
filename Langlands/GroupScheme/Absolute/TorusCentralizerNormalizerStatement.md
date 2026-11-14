# Statement: the identity component of a maximal-torus centralizer

Worker 75.

`Langlands.GroupScheme.TorusCentralizerNormalizerStatement.{u} : Prop` is a statement-only,
`Prop`-valued definition. This module does not prove it, and it adds no other definitions,
theorems or axioms. It imports:

- [`Nilpotent.Basic`](../Nilpotent/Basic.md), for `IsNilpotentGroupScheme` and, through
  [`Absolute.Borel`](Borel.md), for `IsMaximalTorus`, `IsClosedSubgroup` and the group-scheme
  vocabulary over a field.
- [`Rational.TorusCentralizer`](../Rational/TorusCentralizer.md), for `torusCentralizer`.
- [`Rational.TorusNormalizer`](../Rational/TorusNormalizer.md), for
  `SubgroupFunctor.normalizer`.

## Lean statement

```lean
def TorusCentralizerNormalizerStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (j : T.toGrp ⟶ G), IsMaximalTorus j →
    ∀ (C : GroupScheme (Spec (CommRingCat.of k))) (c : C ⟶ G),
      IsClosedSubgroup c → ConnectedSpace C.X.left →
      SubgroupFunctor.range c ≤ torusCentralizer j →
      (∀ (H : GroupScheme (Spec (CommRingCat.of k))) (h : H ⟶ G),
        IsClosedSubgroup h → ConnectedSpace H.X.left →
          SubgroupFunctor.range h ≤ torusCentralizer j →
            SubgroupFunctor.range h ≤ SubgroupFunctor.range c) →
      Smooth C.X.hom ∧ IsNilpotentGroupScheme C ∧
        ∀ (H : GroupScheme (Spec (CommRingCat.of k))) (h : H ⟶ G),
          IsClosedSubgroup h → ConnectedSpace H.X.left →
            SubgroupFunctor.range h ≤ (SubgroupFunctor.range c).normalizer →
              SubgroupFunctor.range h ≤ SubgroupFunctor.range c
```

## Objects and predicates used

- **Group schemes.** `GroupScheme S` is `Grp (Over S)` and `CommGroupScheme S` its commutative
  version, with `T.toGrp` the underlying group scheme. For `G : GroupScheme S`, `G.X.left` is
  the underlying scheme and `G.X.hom` its structure morphism.
- `Smooth`, `IsAffineHom`, `ConnectedSpace`: as in Mathlib.
- `IsMaximalTorus j` ([`Torus.Maximal`](../Torus/Maximal.md)): `T` is a torus, `j` is a closed
  immersion, and `j` does not factor through a strictly larger closed torus of `G`.
- `IsClosedSubgroup c` ([`Reductive.Basic`](../Reductive/Basic.md)): the underlying morphism
  of schemes of `c` is a closed immersion.
- `SubgroupFunctor.range c`: the points of `G`, over schemes over `Spec k`, that factor through
  `c`; subgroup functors are ordered by inclusion of points.
- `torusCentralizer j` ([`Rational.TorusCentralizer`](../Rational/TorusCentralizer.md)): a point
  `g` over `U` lies in it when, after every base change `a : V ⟶ U`, the point `a ≫ g` commutes
  with the image of every point of `T` over `V`. This is the centralizer `C_G(T)`.
- `F.normalizer` ([`Rational.TorusNormalizer`](../Rational/TorusNormalizer.md)): a point `g`
  over `U` lies in it when, after every base change `a : V ⟶ U`, conjugation by `a ≫ g` and by
  its inverse preserves the points of `F` over `V`.
- `IsNilpotentGroupScheme C` ([`Nilpotent.Basic`](../Nilpotent/Basic.md)): the abstract group of
  points of `C` over an algebraic closure of `k` is nilpotent.

## Statement and quantifiers

Let `k : Type u` be algebraically closed, `G` a smooth, affine, connected group scheme over
`Spec k`, and `j : T.toGrp ⟶ G` a maximal torus. Let `c : C ⟶ G` be a closed subgroup with `C`
connected, contained in `C_G(T)`, and containing every connected closed subgroup of `G`
contained in `C_G(T)`. Then:

1. `C` is smooth over `k`;
2. `C` is nilpotent;
3. every connected closed subgroup `h : H ⟶ G` contained in the normalizer of `C` is contained
   in `C`.

**Why the hypotheses on `c` describe `C_G(T)°`.** The centralizer `C_G(T)` is represented by a
closed subgroup of `G`, and its identity component `C_G(T)°` is a connected closed subgroup
inside `C_G(T)`. Any connected closed subgroup inside `C_G(T)` lands in `C_G(T)°`: it is
connected and contains `e`, and `C_G(T)°` is open in `C_G(T)`. So `C_G(T)°` is the largest
connected closed subgroup inside `C_G(T)`, and `c` satisfies the hypotheses exactly when its
range is that of `C_G(T)°`. The statement does not assert that such a `c` exists.

**Why point 3 says `C = N_G(C)°`.** The normalizer `N_G(C)` of the closed subgroup `C` of the
affine group `G` is represented by a closed subgroup, and `C ⊆ N_G(C)°` because `C` is
connected and normalizes itself. Point 3 applied to `N_G(C)°` gives the reverse inclusion.
Conversely, point 3 follows from `N_G(C)° = C`, since a connected closed subgroup inside
`N_G(C)` lies in `N_G(C)°`.

## Source

James S. Milne, *Algebraic Groups: The theory of group schemes of finite type over a field*
(Cambridge University Press, 2017), source ID `milne-2017-algebraic-groups`, file
`Milne--Algebraic groups, the theory of group schemes of finite type over a field
(book)--2017.pdf`. Page numbers are printed page numbers; the PDF page is the printed page
plus 16.

- Proposition 17.28, p.360: "Let T be a maximal torus of G. Then C_G(T)° is smooth, nilpotent,
  and equals N_G(C)°." In the proof, `C` denotes `C_G(T)°`.
- Section 17b, opening, p.353: "In this section, G is a connected group variety over an
  algebraically closed field k."
- Chapter 17 opening, p.352: all algebraic groups are affine over the base field; p.13:
  "group variety" = "smooth algebraic group".

The official errata snapshot of 2026-11-02 (source ID
`milne-2017-algebraic-groups-errata-2026-11-02`) lists Chapter 17 corrections only on pp.360,
364 and 386. The p.360 entry corrects the sentence before 17.28 ("SL₂ (not SL₃) has dimension
3"); it does not concern Proposition 17.28.

Milne's proof: `C` is smooth by 13.10 and contains `T` in its centre, so it is nilpotent by
17.23; by 16.47, `C = U × T` with the decomposition preserved by automorphisms, so `N_G(C)°`
preserves `T` and centralizes it by rigidity (12.37), whence `C ⊂ N_G(C)° ⊂ C_G(T)° = C`. This is
explanation only.

## Derivation from the source

- **Connected group variety.** As in Section 17b: `[IsAlgClosed k]`, `[Smooth G.X.hom]`,
  `[IsAffineHom G.X.hom]`, `[ConnectedSpace G.X.left]`.
- **`C_G(T)°` and `N_G(C)°`.** The Library has no identity-component construction for
  arbitrary closed subgroups, so both identity components are expressed through their maximality
  among connected closed subgroups, as explained above.
- **Nilpotence.** For smooth groups the Library measures nilpotence through the abstract group of
  `k̄`-points; here `k` is algebraically closed and `C` is smooth by point 1, where this agrees
  with Milne's Definition 6.34.

## Related Library results

- [`Cartan.StructureStatement`](../Cartan/StructureStatement.md) states Milne's
  Proposition 17.44 over any field: a Cartan subgroup (a closed representative of `C_G(T)`) is
  smooth, connected and nilpotent. Combined with connectedness of `C_G(T)`, it gives points 1
  and 2; point 3 is not part of it.
- [`Cartan.Basic`](../Cartan/Basic.md) shows that every maximal torus of an affine group over a
  field has a closed representative of its centralizer.
