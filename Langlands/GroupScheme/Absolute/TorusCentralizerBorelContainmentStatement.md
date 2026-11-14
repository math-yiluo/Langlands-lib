# Statement: Borel subgroups through a maximal torus contain its centralizer

Worker 75.

`Langlands.GroupScheme.TorusCentralizerBorelContainmentStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no other
definitions, theorems or axioms. It imports:

- [`Absolute.Borel`](Borel.md), for `IsBorelSubgroup`, `IsMaximalTorus`, `IsClosedSubgroup` and
  the group-scheme vocabulary over a field.
- [`Rational.TorusCentralizer`](../Rational/TorusCentralizer.md), for `torusCentralizer`.

## Lean statement

```lean
def TorusCentralizerBorelContainmentStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (j : T.toGrp ⟶ G), IsMaximalTorus j →
    ∀ (B : GroupScheme (Spec (CommRingCat.of k))) (i : B ⟶ G), IsBorelSubgroup i →
      SubgroupFunctor.range j ≤ SubgroupFunctor.range i →
      ∀ (H : GroupScheme (Spec (CommRingCat.of k))) (h : H ⟶ G),
        IsClosedSubgroup h → ConnectedSpace H.X.left →
          SubgroupFunctor.range h ≤ torusCentralizer j →
            SubgroupFunctor.range h ≤ SubgroupFunctor.range i
```

## Objects and predicates used

- **Group schemes.** `GroupScheme S` is `Grp (Over S)` and `CommGroupScheme S` its commutative
  version, with `T.toGrp` the underlying group scheme. For `G : GroupScheme S`, `G.X.left` is
  the underlying scheme and `G.X.hom` its structure morphism.
- `Smooth`, `IsAffineHom`, `ConnectedSpace`: as in Mathlib.
- `IsMaximalTorus j` ([`Torus.Maximal`](../Torus/Maximal.md)): `T` is a torus, `j` is a closed
  immersion, and `j` does not factor through a strictly larger closed torus of `G`.
- `IsBorelSubgroup i` ([`Absolute.Borel`](Borel.md)): `i` is a closed immersion, `B` is smooth,
  connected and solvable, and `i` does not factor through a strictly larger smooth connected
  solvable closed subgroup.
- `IsClosedSubgroup h` ([`Reductive.Basic`](../Reductive/Basic.md)): the underlying morphism
  of schemes of `h` is a closed immersion.
- `SubgroupFunctor.range`: the points of `G` that factor through the given homomorphism;
  subgroup functors are ordered by inclusion of points.
- `torusCentralizer j` ([`Rational.TorusCentralizer`](../Rational/TorusCentralizer.md)): the
  centralizer `C_G(T)`, tested after every base change.

## Statement and quantifiers

For every algebraically closed field `k : Type u`, every smooth, affine, connected group scheme
`G` over `Spec k`, every maximal torus `j : T.toGrp ⟶ G` and every Borel subgroup `i : B ⟶ G`
containing `T`: every closed subgroup `h : H ⟶ G` with `H` connected and contained in `C_G(T)`
is contained in `B`.

**Why this says `C_G(T)° ⊆ B`.** The centralizer `C_G(T)` is represented by a closed subgroup
of `G`, and its identity component `C_G(T)°` is the largest connected closed subgroup of `G`
inside `C_G(T)`: a connected closed subgroup inside `C_G(T)` contains `e` and so lands in the
open and closed subgroup `C_G(T)°`. Taking `h` to represent `C_G(T)°` gives `C_G(T)° ⊆ B`;
conversely `C_G(T)° ⊆ B` gives the statement for every such `h`.

## Source

James S. Milne, *Algebraic Groups: The theory of group schemes of finite type over a field*
(Cambridge University Press, 2017), source ID `milne-2017-algebraic-groups`, file
`Milne--Algebraic groups, the theory of group schemes of finite type over a field
(book)--2017.pdf`. Page numbers are printed page numbers; the PDF page is the printed page
plus 16.

- Corollary 17.29, p.360: "Let T be a maximal torus of G. Then C_G(T)° is contained in every
  Borel subgroup of G containing T."
- Section 17b, opening, p.353: "In this section, G is a connected group variety over an
  algebraically closed field k."
- Definition 17.6, p.353: a Borel subgroup is a maximal connected solvable subgroup variety.
- Chapter 17 opening, p.352: all algebraic groups are affine over the base field; p.13:
  "group variety" = "smooth algebraic group".

The official errata snapshot of 2026-11-02 (source ID
`milne-2017-algebraic-groups-errata-2026-11-02`) lists Chapter 17 corrections only on pp.360,
364 and 386. The p.360 entry corrects the remark before 17.28 ("SL₂ (not SL₃) has dimension
3"); it does not concern Corollary 17.29.

Milne's proof: `C_G(T)°` is connected and nilpotent (17.28), so it lies in some Borel subgroup
`B'`; the Borel subgroups containing `T` are conjugate under `N_G(T)(k)` (17.11), and
conjugating gives `C_G(T)° ⊆ B`. This is explanation only.

## Derivation from the source

- **Connected group variety.** As in Section 17b: `[IsAlgClosed k]`, `[Smooth G.X.hom]`,
  `[IsAffineHom G.X.hom]`, `[ConnectedSpace G.X.left]`.
- **Containment.** "`B` contains `T`" and "`C_G(T)°` is contained in `B`" are inclusions of
  subgroups of `G`, encoded by `≤` between ranges.
- **`C_G(T)°`.** The Library has no identity-component construction for arbitrary closed
  subgroups, so `C_G(T)°` is expressed through its maximality among connected closed subgroups
  inside `C_G(T)`, as explained above.

## Related Library results

- [`Absolute.SolvableSubgroupBorelContainmentStatement`](SolvableSubgroupBorelContainmentStatement.md)
  states that every smooth connected solvable closed subgroup lies in a Borel subgroup, an input
  to Milne's proof.
- [`Cartan.StructureStatement`](../Cartan/StructureStatement.md) states that a Cartan subgroup
  (a closed representative of `C_G(T)`) is smooth, connected and nilpotent.
