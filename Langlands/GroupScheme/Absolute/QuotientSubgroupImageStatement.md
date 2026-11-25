# Statement: quotient maps and parabolic, Borel, maximal unipotent and maximal toric subgroups

`Langlands.GroupScheme.AlgClosedQuotientSubgroupImageStatement.{u} : Prop` is a statement-only,
`Prop`-valued definition. This module does not prove it, and it adds no other definitions,
theorems or axioms. It imports [`Absolute.Borel`](Borel.md), for `IsBorelSubgroup` and
`IsParabolicSubgroup`, and through its imports `IsMaximalTorus`, `IsUnipotent`,
`IsClosedSubgroup` and the group-scheme vocabulary over a field.

## Lean statement

```lean
def AlgClosedQuotientSubgroupImageStatement : Prop :=
  let IsMaximalUnipotent :
      ∀ {k : Type u} [Field k] {U G : GroupScheme (Spec (CommRingCat.of k))}, (U ⟶ G) → Prop :=
    fun {k} _ {U G} u => IsClosedSubgroup u ∧ Smooth U.X.hom ∧ ConnectedSpace U.X.left ∧
      IsUnipotent U ∧
      ∀ (U' : GroupScheme (Spec (CommRingCat.of k))) (u' : U' ⟶ G) (f : U ⟶ U'),
        IsClosedSubgroup u' → Smooth U'.X.hom → ConnectedSpace U'.X.left → IsUnipotent U' →
          f ≫ u' = u → IsIso f
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (G Q : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    [Smooth Q.X.hom] [IsAffineHom Q.X.hom] [ConnectedSpace Q.X.left]
    (q : G ⟶ Q), Flat q.hom.hom.left → Surjective q.hom.hom.left →
    (∀ (H H' : GroupScheme (Spec (CommRingCat.of k))) (i : H ⟶ G) (j : H' ⟶ Q) (f : H ⟶ H'),
      IsClosedSubgroup j → Smooth H'.X.hom → Surjective f.hom.hom.left → i ≫ q = f ≫ j →
        (IsParabolicSubgroup i → IsParabolicSubgroup j) ∧
        (IsBorelSubgroup i → IsBorelSubgroup j) ∧
        (IsMaximalUnipotent i → IsMaximalUnipotent j)) ∧
    (∀ (T S : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
      (j : S.toGrp ⟶ Q) (f : T ⟶ S),
      IsClosedSubgroup j → Smooth S.X.hom → Surjective (CommGroupScheme.groupHom f).hom.hom.left →
        i ≫ q = CommGroupScheme.groupHom f ≫ j → IsMaximalTorus i → IsMaximalTorus j) ∧
    (∀ (H' : GroupScheme (Spec (CommRingCat.of k))) (j : H' ⟶ Q), IsParabolicSubgroup j →
      ∃ (H : GroupScheme (Spec (CommRingCat.of k))) (i : H ⟶ G) (f : H ⟶ H'),
        IsParabolicSubgroup i ∧ Surjective f.hom.hom.left ∧ i ≫ q = f ≫ j) ∧
    (∀ (H' : GroupScheme (Spec (CommRingCat.of k))) (j : H' ⟶ Q), IsBorelSubgroup j →
      ∃ (H : GroupScheme (Spec (CommRingCat.of k))) (i : H ⟶ G) (f : H ⟶ H'),
        IsBorelSubgroup i ∧ Surjective f.hom.hom.left ∧ i ≫ q = f ≫ j) ∧
    (∀ (H' : GroupScheme (Spec (CommRingCat.of k))) (j : H' ⟶ Q), IsMaximalUnipotent j →
      ∃ (H : GroupScheme (Spec (CommRingCat.of k))) (i : H ⟶ G) (f : H ⟶ H'),
        IsMaximalUnipotent i ∧ Surjective f.hom.hom.left ∧ i ≫ q = f ≫ j) ∧
    (∀ (S : CommGroupScheme (Spec (CommRingCat.of k))) (j : S.toGrp ⟶ Q), IsMaximalTorus j →
      ∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G) (f : T ⟶ S),
        IsMaximalTorus i ∧ Surjective (CommGroupScheme.groupHom f).hom.hom.left ∧
          i ≫ q = CommGroupScheme.groupHom f ≫ j)
```

## Objects and predicates used

- **Group schemes.** `GroupScheme S` is `Grp (Over S)` and `CommGroupScheme S` the commutative
  group schemes; `T.toGrp` is the underlying group scheme of `T` and
  `CommGroupScheme.groupHom f` the underlying homomorphism of `f : T ⟶ S`. For a group scheme
  `G`, `G.X.left` is its underlying scheme and `G.X.hom` its structure morphism. For a
  homomorphism `q : G ⟶ Q`, `q.hom.hom.left` is the underlying morphism of schemes.
- `IsAlgClosed`, `Smooth`, `IsAffineHom`, `ConnectedSpace`, `Flat`, `Surjective`, `IsIso`: as in
  Mathlib. `Surjective` is surjectivity of the map of underlying topological spaces.
- `IsClosedSubgroup u`: the underlying morphism of `u` is a closed immersion.
- `IsUnipotent U` ([`Reductive.Basic`](../Reductive/Basic.md)): every nonzero
  finite-dimensional representation of `U` has a nonzero fixed vector.
- `IsBorelSubgroup i` ([`Absolute.Borel`](Borel.md)): `i` is a closed immersion, `H` is smooth,
  connected and solvable, and `i` does not factor through a strictly larger smooth connected
  solvable closed subgroup.
- `IsParabolicSubgroup i` ([`Absolute.Borel`](Borel.md)): `i` is a closed immersion, `H` is
  smooth, and some Borel subgroup of `G_{k̄}` factors through `i_{k̄}`, with `k̄` the algebraic
  closure `AlgebraicClosure k`.
- `IsMaximalTorus i` ([`Torus.Maximal`](../Torus/Maximal.md)): `T` is a torus, `i` is a closed
  immersion, and `i` does not factor through a strictly larger torus of `G` that is a closed
  immersion.
- `IsMaximalUnipotent u` (local `let`, used only inside this statement): `u` is a closed
  immersion, `U` is smooth, connected and unipotent, and `u` does not factor through a strictly
  larger smooth connected unipotent closed subgroup: whenever `f ≫ u' = u` with `u'` such a
  subgroup, `f` is an isomorphism. This is the pattern of `IsBorelSubgroup` with "unipotent" in
  place of "solvable".

## Statement and quantifiers

Let `k : Type u` be an algebraically closed field, `G` and `Q` smooth, affine, connected group
schemes over `Spec k`, and `q : G ⟶ Q` a homomorphism that is flat and surjective.

**Images.** Call a closed subgroup `j : H' ⟶ Q` with `H'` smooth an *image* of `i : H ⟶ G` when
there is a homomorphism `f : H ⟶ H'`, surjective on underlying spaces, with `i ≫ q = f ≫ j`.
Then:

1. if `i` is parabolic, so is `j`;
2. if `i` is a Borel subgroup, so is `j`;
3. if `i` is a maximal smooth connected unipotent closed subgroup, so is `j`;
4. if `i : T ⟶ G` is a maximal torus, `S` is commutative, and `j : S ⟶ Q` is an image of `i` in
   the above sense (through a homomorphism `f : T ⟶ S` of commutative group schemes), then `j`
   is a maximal torus of `Q`.

**Every such subgroup of `Q` is an image.**

5. For every parabolic `j : H' ⟶ Q` there is a parabolic `i : H ⟶ G` and a surjective
   `f : H ⟶ H'` with `i ≫ q = f ≫ j`;
6. likewise for Borel subgroups;
7. likewise for maximal smooth connected unipotent closed subgroups;
8. likewise for maximal tori, with `T`, `S` commutative and `f : T ⟶ S`.

**Why this encodes `q(H)`.** Milne's image `q(H)` is the smallest algebraic subgroup of `Q`
through which `q|H` factors, and `H ⟶ q(H)` is surjective (Remark 5.42, p.108). If `j : H' ⟶ Q`
is a closed subgroup, `f` is surjective and `i ≫ q = f ≫ j`, then `q(H) ⊆ H'` and both have
underlying space `q(|H|)`. When `H'` is reduced, as it is here because it is smooth, this forces
`H' = q(H)`. Conversely, for a smooth `H` the image `q(H)` is smooth (it is a quotient of `H`,
Proposition 1.62(b), p.24), so `j = (q(H) ⊆ Q)` with `f = (H ⟶ q(H))` satisfies the hypotheses
of items 1-4. In items 5-8 the subgroup `H'` is smooth, since each of the four predicates
includes smoothness, so the equation `i ≫ q = f ≫ j` with `f` surjective says exactly
`q(H) = H'`. In item 4 the hypothesis is that `S` is commutative and smooth; the image of a torus
is commutative, and the conclusion `IsMaximalTorus j` includes that `S` is a torus.

## Source

James S. Milne, *Algebraic Groups: The theory of group schemes of finite type over a field*
(Cambridge University Press, 2017), source ID `milne-2017-algebraic-groups`, file
`Milne--Algebraic groups, the theory of group schemes of finite type over a field
(book)--2017.pdf`. Page numbers are printed page numbers; the PDF page is the printed page
plus 16.

- Proposition 17.20, pp.357-358: "Let q: G → Q be a quotient map of connected group varieties,
  and let H be a subgroup variety of G. If H is parabolic (resp. Borel, resp. a maximal
  unipotent subgroup variety, resp. a maximal torus), then so also is q(H); moreover, every such
  subgroup of Q arises in this way."
- Section 17b opening, p.353: "In this section, G is a connected group variety over an
  algebraically closed field k." Definition 17.6, p.353: "A Borel subgroup of G is a maximal
  connected solvable subgroup variety of G."
- Proposition 17.14, p.356: "The maximal connected unipotent subgroup varieties of G are those
  of the form B_u with B a Borel subgroup of G."
- Definition 17.15 and Theorem 17.16, p.356: a subgroup variety `P` is parabolic if `G/P` is
  complete, and this holds if and only if `P` contains a Borel subgroup.
- Definition 5.5, p.99: "A homomorphism of algebraic groups is a quotient map if it is faithfully
  flat. Thus a homomorphism is a quotient map if it is both flat and surjective."
- Theorem 5.39 and Remark 5.42, p.108: the image `φ(G)` of a homomorphism `φ : G → H` "is the
  smallest algebraic subgroup of H through which φ factors. The morphism φ: G → φ(G) is
  surjective".
- Proposition 1.62(b), p.24, and the sentence after it: "quotients of group varieties are group
  varieties".
- Chapter 17 opening, p.352: all algebraic groups are affine over the base field; remark after
  1.26, p.13: "group variety" means "smooth algebraic group".

The official errata snapshot of 2026-11-02 (source ID
`milne-2017-algebraic-groups-errata-2026-11-02`) lists Chapter 1 corrections only on pp.18, 20,
21 and 26, Chapter 5 corrections only on p.123, and Chapter 17 corrections only on pp.360, 364
and 386. None concerns the items above.

Milne's proof, in outline. The map `G → Q/q(H)` factors through `G/H`, giving a surjection
`G/H → Q/q(H)`. If `H` is parabolic, `Q/q(H)` is complete (A.75d), so `q(H)` is parabolic. If `H`
is a Borel subgroup, `q(H)` is connected (5.59) and solvable (6.27) with `Q/q(H)` complete, so
`q(H)` is a Borel subgroup (17.19). If `H` is a maximal unipotent subgroup variety, `H = B_u` for
a Borel subgroup `B` (17.14); `q(B_u)` is a normal unipotent subgroup of the Borel subgroup
`q(B)` with `q(B)/q(B_u)` of multiplicative type, so `q(B_u) = q(B)_u`, which is maximal (17.14).
If `H` is a maximal torus, it lies in a Borel subgroup `B` with `B = B_u ⋊ H` (16.33), so
`q(B) = q(B)_u ⋊ q(H)` and `q(H)` is a maximal torus of `q(B)`, hence of `Q`. For the converse, a
Borel subgroup `B'` of `Q` is `q(g) q(B) q(g)⁻¹ = q(g B g⁻¹)` for a Borel subgroup `B` of `G`
and some `g ∈ G(k)` (Theorem 17.9). "The same argument applies to maximal unipotent subgroup
varieties and maximal tori of Q." A parabolic subgroup `H'` of `Q` contains some `B' = q(B)`,
so `q⁻¹(H')_red` contains `B`, is parabolic, and has image `H'`. This is explanation only.

## Derivation from the source

- **Algebraically closed field; connected group varieties.** `[IsAlgClosed k]` is the standing
  assumption of Section 17b. `G` and `Q` are smooth (`group variety`), affine (Chapter 17
  convention) and connected.
- **Quotient map.** By Definition 5.5, a quotient map is a flat surjective homomorphism:
  `Flat q.hom.hom.left` and `Surjective q.hom.hom.left`.
- **Subgroup variety `H` and its image `q(H)`.** A subgroup variety is a smooth closed subgroup.
  Each of the four predicates on `i` includes that `i` is a closed immersion with smooth source,
  so `H` is a subgroup variety whenever a hypothesis of items 1-4 holds. The image is encoded as
  explained under "Why this encodes `q(H)`".
- **Parabolic.** `IsParabolicSubgroup`, which by its documentation is Definition 17.15 through
  Theorem 17.16. Since `k` is algebraically closed, the base change to `k̄` changes nothing
  mathematically.
- **Borel.** `IsBorelSubgroup`, which over an algebraically closed field is Definition 17.6.
- **Maximal unipotent subgroup variety.** Milne's proof treats this case with Proposition 17.14,
  which describes the maximal *connected* unipotent subgroup varieties. The statement uses that
  reading: `IsMaximalUnipotent`, maximal among smooth connected unipotent closed subgroups and
  itself connected.
- **Maximal torus.** `IsMaximalTorus`, a torus maximal among tori, which over an algebraically
  closed field is the notion of Section 17b.
- **"Every such subgroup of `Q` arises in this way."** Items 5-8: each subgroup of `Q` of one of
  the four kinds is `q(H)` for a subgroup `H` of `G` of the same kind.

## Scope

- The field is algebraically closed, as in Section 17b. Over an arbitrary field, the image part
  for parabolic and Borel subgroups is Milne 17.69, stated as `QuotientParabolicImageStatement`
  (module `Rational.QuotientParabolicImageStatement`, proved as `quotientParabolicImage` in
  `Rational.QuotientParabolicImageProof`).
- The statement does not construct `q(H)` or `q⁻¹(H')`. It does not state Theorem 17.9 or
  Proposition 17.14 themselves.

## Related Library results

- `CentralIsogenyMaximalTorusImageStatement`
  ([`CentralIsogeny.MaximalTorusImageStatement`](../CentralIsogeny/MaximalTorusImageStatement.md))
  is the maximal-torus image part for central isogenies of connected reductive groups over an
  arbitrary field, derived from Proposition 17.20 and Theorem 17.82. It is proved as
  `centralIsogenyMaximalTorusImage`
  ([`CentralIsogeny.MaximalTorusImageProof`](../CentralIsogeny/MaximalTorusImageProof.md)).
- `AdjointQuotientQuasiSplitStatement`
  ([`Adjoint.QuasiSplitStatement`](../Adjoint/QuasiSplitStatement.md)) says that the adjoint
  quotient of a quasi-split connected reductive group over an arbitrary field is quasi-split,
  derived from the Borel image parts of 17.20 and 17.69. It is proved as
  `adjointQuotientQuasiSplitStatement` ([`Adjoint.QuasiSplitProof`](../Adjoint/QuasiSplitProof.md)).
