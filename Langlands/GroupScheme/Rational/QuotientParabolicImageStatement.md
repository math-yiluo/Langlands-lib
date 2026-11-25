# Statement: quotient maps carry parabolic and Borel subgroups to parabolic and Borel subgroups

`Langlands.GroupScheme.QuotientParabolicImageStatement.{u} : Prop` is a statement-only,
`Prop`-valued definition. This module does not prove it, and it adds no other definitions,
theorems or axioms. It imports [`Reductive.QuasiSplit`](../Reductive/QuasiSplit.md), for
`IsGeometricBorelSubgroup` and, through its imports, `IsParabolicSubgroup`, `IsBorelSubgroup`,
`IsClosedSubgroup` and the group-scheme vocabulary over a field.

## Lean statement

```lean
def QuotientParabolicImageStatement : Prop :=
  ∀ (k : Type u) [Field k] (G Q : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    [Smooth Q.X.hom] [IsAffineHom Q.X.hom] [ConnectedSpace Q.X.left]
    (q : G ⟶ Q), Flat q.hom.hom.left → Surjective q.hom.hom.left →
    ∀ (H H' : GroupScheme (Spec (CommRingCat.of k))) (i : H ⟶ G) (j : H' ⟶ Q) (f : H ⟶ H'),
      IsClosedSubgroup j → Smooth H'.X.hom → Surjective f.hom.hom.left → i ≫ q = f ≫ j →
        (IsParabolicSubgroup i → IsParabolicSubgroup j) ∧
        (IsGeometricBorelSubgroup i → IsGeometricBorelSubgroup j)
```

## Objects and predicates used

- **Group schemes.** `GroupScheme S` is `Grp (Over S)`. For a group scheme `G`, `G.X.left` is
  its underlying scheme and `G.X.hom` its structure morphism. For a homomorphism `q : G ⟶ Q`,
  `q.hom.hom.left` is the underlying morphism of schemes.
- `Smooth`, `IsAffineHom`, `ConnectedSpace`, `Flat`, `Surjective`: as in Mathlib. `Surjective`
  is surjectivity of the map of underlying topological spaces.
- `IsClosedSubgroup j`: the underlying morphism of `j` is a closed immersion.
- `IsParabolicSubgroup i` ([`Absolute.Borel`](../Absolute/Borel.md)): `i` is a closed immersion,
  `H` is smooth, and some Borel subgroup of `G_{k̄}` factors through `i_{k̄}`, with `k̄` the
  algebraic closure `AlgebraicClosure k`.
- `IsBorelSubgroup i` ([`Absolute.Borel`](../Absolute/Borel.md)): `i` is a closed immersion, `H`
  is smooth, connected and solvable, and `i` does not factor through a strictly larger smooth
  connected solvable closed subgroup defined over the same field.
- `IsGeometricBorelSubgroup i` ([`Reductive.QuasiSplit`](../Reductive/QuasiSplit.md)):
  `IsBorelSubgroup i` holds, and so does `IsBorelSubgroup` of the base change of `i` to
  `AlgebraicClosure k`.

## Statement and quantifiers

Let `k : Type u` be an arbitrary field, `G` and `Q` smooth, affine, connected group schemes over
`Spec k`, and `q : G ⟶ Q` a homomorphism that is flat and surjective. Let `i : H ⟶ G` be a
homomorphism, `j : H' ⟶ Q` a closed subgroup with `H'` smooth, and `f : H ⟶ H'` a homomorphism
that is surjective on underlying spaces, with `i ≫ q = f ≫ j`. Then:

1. if `i` is parabolic, so is `j`;
2. if `i` is a geometric Borel subgroup, so is `j`.

**Why this encodes `q(H)`.** Milne's image `q(H)` is the smallest algebraic subgroup of `Q`
through which `q|H` factors, and `H ⟶ q(H)` is surjective (Remark 5.42, p.108). Given `j`, `f`
as above, `q(H) ⊆ H'` and both have underlying space `q(|H|)`. As `H'` is smooth, hence reduced,
`H' = q(H)`. Conversely, for a smooth `H` the image `q(H)` is smooth (it is a quotient of `H`,
Proposition 1.62(b), p.24), so `j = (q(H) ⊆ Q)` with `f = (H ⟶ q(H))` satisfies the hypotheses.
Both predicates on `i` include that `i` is a closed immersion with smooth source, so `H` is a
subgroup variety whenever a hypothesis holds.

## Source

James S. Milne, *Algebraic Groups: The theory of group schemes of finite type over a field*
(Cambridge University Press, 2017), source ID `milne-2017-algebraic-groups`, file
`Milne--Algebraic groups, the theory of group schemes of finite type over a field
(book)--2017.pdf`. Page numbers are printed page numbers; the PDF page is the printed page
plus 16.

- 17.69, p.376: "Let q: G → Q be a quotient map of connected group varieties, and let H be a
  subgroup variety of G. If H is parabolic (resp. Borel), then so also is q(H). This follows
  from Proposition 17.20." It is in Section 17i, "Borel and parabolic subgroups over an arbitrary
  base field" (p.375), where `k` is arbitrary.
- 17.66, p.375: "A Borel subgroup of a connected group variety G over k is a connected solvable
  subgroup variety B such that G/B is complete. … a subgroup variety B of G is Borel if and only
  if B_{k'} is a Borel subgroup of G_{k'} (see 1.34, 6.31). Therefore the Borel subgroups of G
  are exactly those algebraic subgroups that become Borel in the sense of (17.6) over an
  algebraic closure of k."
- Definition 17.15, p.356: "Let G be a connected group variety over a field k (not necessarily
  algebraically closed). A subgroup variety P of G is parabolic if G/P is complete." Theorem
  17.16, p.356 (over an algebraically closed field): `P` is parabolic if and only if it contains
  a Borel subgroup.
- Proposition 17.20, pp.357-358, over an algebraically closed field (Section 17b, p.353): "Let
  q: G → Q be a quotient map of connected group varieties, and let H be a subgroup variety of G.
  If H is parabolic (resp. Borel, resp. a maximal unipotent subgroup variety, resp. a maximal
  torus), then so also is q(H); moreover, every such subgroup of Q arises in this way."
- Definition 5.5, p.99: "A homomorphism of algebraic groups is a quotient map if it is faithfully
  flat. Thus a homomorphism is a quotient map if it is both flat and surjective."
- Theorem 5.39 and Remark 5.42, p.108: the image `φ(G)` of a homomorphism `φ : G → H` "is the
  smallest algebraic subgroup of H through which φ factors. The morphism φ: G → φ(G) is
  surjective".
- Proposition 1.62(b), p.24, and the sentence after it: "quotients of group varieties are group
  varieties". Proposition 1.34, p.16: the identity component is geometrically connected.
- Chapter 17 opening, p.352: all algebraic groups are affine over the base field; remark after
  1.26, p.13: "group variety" means "smooth algebraic group".

The official errata snapshot of 2026-11-02 (source ID
`milne-2017-algebraic-groups-errata-2026-11-02`) lists Chapter 1 corrections only on pp.18, 20,
21 and 26, Chapter 5 corrections only on p.123, and Chapter 17 corrections only on pp.360, 364
and 386. None concerns the items above.

How 17.69 follows from 17.20 (explanation only). Base change everything to `k̄`. Flatness and
surjectivity are stable under base change, and `G_{k̄}`, `Q_{k̄}` are connected (1.34), so
`q_{k̄}` is a quotient map of connected group varieties. The base change `j_{k̄}` is a closed
immersion, `H'_{k̄}` is smooth and `f_{k̄}` is surjective, so `H'_{k̄} = q_{k̄}(H_{k̄})` by the
argument above. If `H_{k̄}` contains a Borel subgroup `B` of `G_{k̄}`, then `q_{k̄}(B)` is a Borel
subgroup of `Q_{k̄}` (17.20) contained in `H'_{k̄}`, so `H'` is parabolic. If `H_{k̄}` is a Borel
subgroup of `G_{k̄}`, then `H'_{k̄} = q_{k̄}(H_{k̄})` is a Borel subgroup of `Q_{k̄}` (17.20).

## Derivation from the source

- **Arbitrary field; connected group varieties.** No hypothesis on `k`. `G` and `Q` are smooth
  (`group variety`), affine (Chapter 17 convention) and connected.
- **Quotient map.** By Definition 5.5, `Flat q.hom.hom.left` and `Surjective q.hom.hom.left`.
- **Subgroup variety `H` and its image `q(H)`.** As explained under "Why this encodes `q(H)`".
- **Parabolic.** `IsParabolicSubgroup`. By its documentation this is Definition 17.15 through
  Theorem 17.16: `G/P` is complete if and only if `G_{k̄}/P_{k̄}` is, which holds if and only if
  `P_{k̄}` contains a Borel subgroup of `G_{k̄}`.
- **Borel over `k`.** By 17.66 the Borel subgroups of `G` are the algebraic subgroups that become
  Borel over `k̄`; this is `IsGeometricBorelSubgroup`. Its first component `IsBorelSubgroup i`
  follows mathematically from the second (for a closed subgroup the Library proves this in
  `isGeometricBorelSubgroup_of_baseChange_toAlgebraicClosure`, module
  `Absolute.GeometricBorelDescent`): a smooth connected
  solvable closed subgroup of `G` containing `H` becomes one of `G_{k̄}` containing `H_{k̄}`, so it
  equals `H`.

## Scope

- Only the image part for parabolic and Borel subgroups is stated, as in 17.69. Over an
  algebraically closed field, Proposition 17.20 in full (also maximal unipotent subgroups and
  maximal tori, and the converse that every such subgroup of `Q` is an image) is stated as
  `AlgClosedQuotientSubgroupImageStatement` (module
  `Absolute.QuotientSubgroupImageStatement`), proved as `algClosedQuotientSubgroupImage`
  ([`Absolute.QuotientSubgroupImageProof`](../Absolute/QuotientSubgroupImageProof.md)).
- `Q` need not be reductive and `q` need not be central.

## Related Library results

- `AdjointQuotientQuasiSplitStatement`
  ([`Adjoint.QuasiSplitStatement`](../Adjoint/QuasiSplitStatement.md)) says that the adjoint
  quotient of a quasi-split connected reductive group is quasi-split. It is derived from 17.20
  and 17.69, by item 2 applied to an adjoint quotient `q`. It is proved as `adjointQuotientQuasiSplitStatement`
  ([`Adjoint.QuasiSplitProof`](../Adjoint/QuasiSplitProof.md)).
- `CentralIsogenyMaximalTorusImageStatement`
  ([`CentralIsogeny.MaximalTorusImageStatement`](../CentralIsogeny/MaximalTorusImageStatement.md))
  is the analogous image statement for maximal tori under central isogenies over an arbitrary
  field. It is proved as `centralIsogenyMaximalTorusImage`
  ([`CentralIsogeny.MaximalTorusImageProof`](../CentralIsogeny/MaximalTorusImageProof.md)).
