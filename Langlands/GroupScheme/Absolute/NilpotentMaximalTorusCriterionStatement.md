# Statement: nilpotence criteria through maximal tori and Borel subgroups

Worker 75.

`Langlands.GroupScheme.NilpotentMaximalTorusCriterionStatement.{u} : Prop` is a
statement-only, `Prop`-valued definition. This module does not prove it, and it adds no other
definitions, theorems or axioms. It imports:

- [`Nilpotent.Basic`](../Nilpotent/Basic.md), for `IsNilpotentGroupScheme` and, through
  [`Absolute.Borel`](Borel.md), for `IsBorelSubgroup`, `IsMaximalTorus` and the group-scheme
  vocabulary over a field.
- [`Rational.Characters`](../Rational/Characters.md), for `IsCentral`.
- Mathlib's `Mathlib.Data.List.TFAE`, for `List.TFAE`.

## Lean statement

```lean
def NilpotentMaximalTorusCriterionStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left],
    List.TFAE
      [∀ (T T' : CommGroupScheme (Spec (CommRingCat.of k))) (j : T.toGrp ⟶ G)
          (j' : T'.toGrp ⟶ G), IsMaximalTorus j → IsMaximalTorus j' →
            SubgroupFunctor.range j = SubgroupFunctor.range j',
        ∃ (B : GroupScheme (Spec (CommRingCat.of k))) (i : B ⟶ G),
          IsBorelSubgroup i ∧ IsNilpotentGroupScheme B,
        IsNilpotentGroupScheme G,
        ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))) (j : T.toGrp ⟶ G),
          IsMaximalTorus j → IsCentral j]
```

## Objects and predicates used

- **Group schemes.** `GroupScheme S` is `Grp (Over S)` and `CommGroupScheme S` its commutative
  version, with `T.toGrp` the underlying group scheme. For `G : GroupScheme S`, `G.X` is its
  scheme over `S`; `G.X.left` is the underlying scheme and `G.X.hom` its structure morphism.
  A morphism `j : T.toGrp ⟶ G` is a homomorphism of group schemes over `S`.
- `Smooth G.X.hom`, `IsAffineHom G.X.hom`: Mathlib's smooth and affine morphisms.
  `ConnectedSpace G.X.left`: the underlying space of `G` is connected (and nonempty).
- `IsMaximalTorus j` ([`Torus.Maximal`](../Torus/Maximal.md)): `T` is a torus, `j` is a
  closed immersion, and `j` does not factor through a strictly larger closed torus of `G`.
- `IsBorelSubgroup i` ([`Absolute.Borel`](Borel.md)): `i` is a closed immersion, `B` is smooth,
  connected and solvable, and `i` does not factor through a strictly larger smooth connected
  solvable closed subgroup.
- `IsNilpotentGroupScheme G` ([`Nilpotent.Basic`](../Nilpotent/Basic.md)): the abstract group
  of points of `G` over an algebraic closure `k̄` of `k` is nilpotent. This is the Library's
  nilpotence predicate for smooth groups over a field.
- `SubgroupFunctor.range j`: the subgroup functor of points of `G`, over every scheme over
  `Spec k`, that factor through `j`.
- `IsCentral j` ([`Rational.Characters`](../Rational/Characters.md)): every point of `T`, over
  every scheme over `Spec k`, maps into the centre `center G` of `G`, the all-test subgroup
  functor of points commuting with every point after every base change.
- `List.TFAE [p₁, p₂, p₃, p₄]`: any two of the four propositions are equivalent.

## Statement and quantifiers

For every algebraically closed field `k : Type u` and every group scheme `G` over `Spec k` that
is smooth, affine and connected, the following four conditions are equivalent:

1. any two maximal tori `j : T.toGrp ⟶ G` and `j' : T'.toGrp ⟶ G` have the same range, that
   is, `G` has only one maximal torus as a subgroup;
2. some Borel subgroup `i : B ⟶ G` has `B` nilpotent;
3. `G` is nilpotent;
4. every maximal torus `j : T.toGrp ⟶ G` is central.

Condition 1 says "at most one maximal torus". Since a closed immersion is determined up to
unique isomorphism over `G` by its range, equal ranges mean the same subgroup. Existence of a
maximal torus is not part of condition 1; it is a separate fact about `G`.

## Source

James S. Milne, *Algebraic Groups: The theory of group schemes of finite type over a field*
(Cambridge University Press, 2017), source ID `milne-2017-algebraic-groups`, file
`Milne--Algebraic groups, the theory of group schemes of finite type over a field
(book)--2017.pdf`. Page numbers are printed page numbers; the PDF page is the printed page
plus 16.

- Proposition 17.23, p.359: "The following conditions on G are equivalent: (a) G has only one
  maximal torus; (b) some Borel subgroup of G is nilpotent; (c) G is nilpotent; (d) every
  maximal torus T of G is contained in the centre of G."
- Section 17b, opening, p.353: "In this section, G is a connected group variety over an
  algebraically closed field k."
- Definition 17.6, p.353: "A Borel subgroup of G is a maximal connected solvable subgroup
  variety of G."
- Chapter 17 opening, p.352: all algebraic groups are affine over the base field.
- p.13, after Proposition 1.26: "group variety" = "smooth algebraic group".
- Definition 6.34, p.133: an algebraic group is nilpotent if it admits a central subnormal
  series.

The official errata snapshot of 2026-11-02 (source ID
`milne-2017-algebraic-groups-errata-2026-11-02`) lists Chapter 17 corrections only on pp.360,
364 and 386. None concerns Proposition 17.23.

Milne's proof: (a)⇒(b) shows the maximal torus `T` of a Borel pair is normal in `B` and that
`B ≅ T × U` with `U` unipotent; (b)⇒(c) uses induction on `dim B`, with `Z(B) ⊂ Z(G)`
(17.22) and passage to `G/Z(B)` (17.20); (c)⇒(d) uses Theorem 16.47(a); (d)⇒(a) uses
conjugacy of maximal tori (17.10). This is explanation only.

## Derivation from the source

- **Connected group variety.** In Section 17b, `G` is a connected group variety over an
  algebraically closed field. With the Chapter 17 convention, that is a smooth, affine,
  connected group scheme of finite type over `k`, encoded by `[IsAlgClosed k]`,
  `[Smooth G.X.hom]`, `[IsAffineHom G.X.hom]` and `[ConnectedSpace G.X.left]`.
- **Maximal tori and Borel subgroups.** Milne's maximal tori and Borel subgroups (17.6) are the
  Library's `IsMaximalTorus` and `IsBorelSubgroup`: subgroup varieties are closed smooth
  algebraic subgroups, and maximality is tested against closed subgroups of the same kind.
- **Only one maximal torus.** Condition (a) becomes equality of the ranges of any two maximal
  tori, as explained above.
- **Nilpotence.** For smooth groups over a field the Library measures nilpotence through the
  abstract group of `k̄`-points. Here `k` is algebraically closed, and for a smooth group over
  an algebraically closed field this agrees with Milne's Definition 6.34 (compare 6.38–6.39).
  The Borel subgroup in condition (b) is smooth, so the same predicate applies to it.
- **Contained in the centre.** Condition (d) asks that every point of `T` lie in the centre of
  `G` after every base change, which is `IsCentral j`.

## Scope

- Example 17.24 (a connected solvable group variety is nilpotent iff it has exactly one maximal
  torus) is a special case and is not stated separately.
- Only algebraically closed fields are covered, as in Milne's Section 17b.

## Related Library results

- [`Nilpotent.CentralTorusStatement`](../Nilpotent/CentralTorusStatement.md) states Milne's
  Theorem 16.47(a),(c) for smooth groups, the input to (c)⇒(d).
- [`Absolute.BorelStatement`](BorelStatement.md) states conjugacy of Borel subgroups (17.9(b))
  and of maximal tori (17.10), the input to (d)⇒(a).
- [`Cartan.StructureStatement`](../Cartan/StructureStatement.md) states Milne's
  Proposition 17.44; Milne's proof of it uses this criterion.
