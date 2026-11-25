# Statement: split Borel subgroups over an arbitrary field

`Langlands.GroupScheme.SplitSolvableBorelConjugacyStatement.{u} : Prop` is a statement-only,
`Prop`-valued definition. This module does not prove it, and it adds no other definitions,
theorems or axioms. It imports:

- [`Reductive.QuasiSplit`](../Reductive/QuasiSplit.md), for `IsGeometricBorelSubgroup` and,
  through its imports, `IsBorelSubgroup` and the group-scheme vocabulary over a field.
- [`SplitSolvable`](../SplitSolvable.md), for `IsSplitSolvableGroupScheme`.

The name is chosen to differ from the existing Library module
`Langlands.GroupScheme.RelativeLevi.SplitBorelConjugacyStatement`
([`RelativeLevi.SplitBorelConjugacyStatement`](../RelativeLevi/SplitBorelConjugacyStatement.md)),
which concerns split Borel subgroups of reductive group schemes over a general base.

## Lean statement

```lean
def SplitSolvableBorelConjugacyStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (B : GroupScheme (Spec (CommRingCat.of k))) (b : B ⟶ G),
    IsGeometricBorelSubgroup b → IsSplitSolvableGroupScheme B →
      (∀ (H : GroupScheme (Spec (CommRingCat.of k))) (h : H ⟶ G),
        IsClosedSubgroup h → IsSplitSolvableGroupScheme H →
          ∃ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
            SubgroupFunctor.range h ≤ SubgroupFunctor.range (b ≫ (G.innerIso g).hom)) ∧
      ∀ (B' : GroupScheme (Spec (CommRingCat.of k))) (b' : B' ⟶ G),
        IsGeometricBorelSubgroup b' → IsSplitSolvableGroupScheme B' →
          ∃ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
            SubgroupFunctor.range (b ≫ (G.innerIso g).hom) = SubgroupFunctor.range b'
```

## Objects and predicates used

- **Group schemes.** `GroupScheme S` is `Grp (Over S)`. For `G : GroupScheme S`, `G.X` is its
  scheme over `S`, `G.X.left` the underlying scheme and `G.X.hom` the structure morphism. A
  point of `G` over `U : Over S` is a morphism `U ⟶ G.X`; a `k`-point is a morphism
  `Over.mk (𝟙 (Spec k)) ⟶ G.X`.
- `Smooth`, `IsAffineHom`: as in Mathlib.
- `IsClosedSubgroup h`: the underlying morphism of schemes of `h` is a closed immersion.
- `IsBorelSubgroup b` ([`Absolute.Borel`](../Absolute/Borel.md)): `b` is a closed immersion,
  `B` is smooth, connected and solvable, and `b` does not factor through a strictly larger
  smooth connected solvable closed subgroup.
- `IsGeometricBorelSubgroup b` ([`Reductive.QuasiSplit`](../Reductive/QuasiSplit.md)):
  `IsBorelSubgroup b` holds, and so does `IsBorelSubgroup` of the base change of `b` to an
  algebraic closure of `k`.
- `IsSplitSolvableGroupScheme H` ([`SplitSolvable`](../SplitSolvable.md)): `H` is smooth,
  affine, connected and solvable, and has a finite series
  `H = H₀ ⊇ H₁ ⊇ ⋯ ⊇ Hₙ = e` of smooth connected closed subgroups, each normal in the previous
  one, whose successive fppf quotients are isomorphic over `k` to `𝔾_a` or `𝔾_m`.
- `SubgroupFunctor.range i` for `i : H ⟶ G`: the subgroup functor of `G` whose points over `U`
  are the points of `G` over `U` that factor through `i`. `≤` is inclusion of points over every
  scheme over `Spec k`, and `=` equality; for closed immersions these are inclusion and equality
  of closed subgroups.
- `G.innerIso g` for a `k`-point `g` ([`InnerAutomorphism`](../InnerAutomorphism.md)): the
  inner automorphism `x ↦ g x g⁻¹` of `G` (`InnerAutomorphism.comp_innerIso_hom`). So
  `range (b ≫ int(g))` is the conjugate subgroup `g B g⁻¹`.

## Statement and quantifiers

For every field `k : Type u`, every smooth affine group scheme `G` over `Spec k` (not assumed
connected) and every split Borel subgroup `b : B ⟶ G`, meaning a geometric Borel subgroup with
`B` split solvable:

- (a) for every closed subgroup `h : H ⟶ G` with `H` split solvable there is a `k`-point `g`
  of `G` with `H ⊆ g B g⁻¹`, that is, `range h ≤ range (b ≫ int(g))`;
- (b) for every split Borel subgroup `b' : B' ⟶ G` there is a `k`-point `g` of `G` with
  `g B g⁻¹ = B'`.

Part (b), with `b` arbitrary, says that any two split Borel subgroups of `G` are conjugate by a
`k`-point.

## Source

James S. Milne, *Algebraic Groups: The theory of group schemes of finite type over a field*
(Cambridge University Press, 2017), source ID `milne-2017-algebraic-groups`, file
`Milne--Algebraic groups, the theory of group schemes of finite type over a field
(book)--2017.pdf`. Page numbers are printed page numbers; the PDF page is the printed page
plus 16.

- Theorem 17.105, pp.384–385: "Let G be a group variety over a field k. (a) If H is a split
  solvable subgroup of G and B is a split Borel subgroup, then H ⊆ gBg⁻¹ for some g ∈ G(k).
  (b) Any two split Borel subgroups of G are conjugate by an element of G(k). (c) If G is
  split, then any two split maximal tori are conjugate by an element of G(k)." Parts (a) and
  (b) are this statement; part (c) is not (see Scope).
- Definition 6.33, p.132: "A solvable algebraic group G over k is split if it admits a
  subnormal series G = G₀ ⊃ G₁ ⊃ ⋯ ⊃ Gₙ = e such that each quotient Gᵢ/Gᵢ₊₁ is isomorphic
  to 𝔾_a or to 𝔾_m." Section 17l, p.384, recalls it.
- Definition 17.101, p.384: "A group variety over k is split if it has a Borel subgroup that
  is split (as a solvable group)." So a split Borel subgroup is a Borel subgroup that is split
  solvable.
- 17.66, p.375: "A Borel subgroup of a connected group variety G over k is a connected solvable
  subgroup variety B such that G/B is complete. … the Borel subgroups of G are exactly those
  algebraic subgroups that become Borel in the sense of (17.6) over an algebraic closure of
  k." Definition 17.6, p.353: over an algebraically closed field a Borel subgroup is a maximal
  connected solvable subgroup variety.
- Chapter 17 opening, p.352: all algebraic groups are affine over the base field; remark after
  1.26, p.13: "group variety" means "smooth algebraic group".

The official errata snapshot of 2026-11-02 (source ID
`milne-2017-algebraic-groups-errata-2026-11-02`) lists Chapter 17 corrections only on pp.360,
364 and 386 (the remark before 17.28, Example 17.42 and Exercise 17-7). None of its entries
for Chapters 6 and 17 concerns Theorem 17.105 or Definition 6.33.

Milne's proof of (a): `H` acts on the complete variety `G/B` by left multiplication and, being
split solvable, has a fixed point `P ∈ (G/B)(k)` (16.51). The inverse image of `P` in `G` is a
`B`-torsor over `k`, trivial because `B` is split (16.55), so `HgB ⊆ gB` for some `g ∈ G(k)`.
Part (b) follows from (a) because all Borel subgroups have the same dimension. This is
explanation only.

## Derivation from the source

- **Group variety.** `[Smooth G.X.hom]` and `[IsAffineHom G.X.hom]` (Chapter 17 convention).
  Theorem 17.105 does not assume `G` connected, and neither does the statement.
- **Borel subgroups.** Milne defines Borel subgroups over an arbitrary field for connected `G`
  (17.66): the algebraic subgroups that become Borel over `k^a`. The statement uses
  `IsGeometricBorelSubgroup b`, which expresses exactly this and is also defined for
  nonconnected `G`. For nonconnected `G` it describes the Borel subgroups of the identity
  component `G°`, because a smooth connected subgroup of `G` (or of `G_{k^a}`) lies in the
  identity component; this is how the statement reads "Borel subgroup" in Theorem 17.105 for
  a group variety that need not be connected. The first component `IsBorelSubgroup b` of
  `IsGeometricBorelSubgroup b` follows mathematically from the second (the Library does not
  prove this): a smooth connected solvable closed subgroup of `G` containing `B` becomes one of
  `G_{k^a}` containing `B_{k^a}`, so it equals `B`.
- **Split solvable.** Milne's split solvable groups (Definition 6.33) are
  `IsSplitSolvableGroupScheme`. A group with such a series is smooth and connected, since
  extensions of smooth connected groups by smooth connected groups are smooth and connected,
  and each member `Gᵢ` of the series is then smooth and connected too; it is affine by the
  convention of Chapter 17. So the explicit smoothness, connectedness and affineness fields
  of `IsSplitSolvableGroupScheme`, and the requirement that the series members be smooth and
  connected, exclude nothing. The quotients `Gᵢ/Gᵢ₊₁` are fppf quotients, as in Milne's
  Definition 5.5 (quotient maps are faithfully flat).
- **Split Borel subgroup.** By Definition 17.101, `b` is a Borel subgroup with `B` split as a
  solvable group: `IsGeometricBorelSubgroup b ∧ IsSplitSolvableGroupScheme B`.
- **Subgroups.** In Milne a subgroup of `G` is an algebraic subgroup, a closed subgroup scheme:
  `IsClosedSubgroup h`.
- **`H ⊆ gBg⁻¹` and conjugacy.** With `g` a `k`-point of `G` and `int(g)` the inner
  automorphism, `gBg⁻¹` is the image of `b ≫ int(g)`. Inclusion and equality of subgroups are
  inclusion and equality of subgroup functors on all schemes over `Spec k`. Part (b) is stated
  for a fixed `b` and every `b'`, which is the same as conjugacy of any two.

## Scope

- Part (c) of Theorem 17.105 (conjugacy of split maximal tori when `G` is split) is not part of
  this statement. For connected `G` it follows from
  `SmoothMaximalSplitTorusConjugacyStatement` (see below), since a maximal torus that is split
  is maximal among split tori.
- The statement does not assert that a split Borel subgroup exists.

## Related Library results

- `SplitSolvableIntoPseudoParabolicStatement`
  ([`SplitSolvableIntoPseudoParabolicStatement`](../SplitSolvableIntoPseudoParabolicStatement.md))
  states Conrad–Gabber–Prasad Lemma C.2.2: a split solvable closed subgroup of a smooth
  connected affine group is conjugate by a `k`-point into any pseudo-parabolic subgroup. It is
  an analogue of (a) with pseudo-parabolic subgroups in place of split Borel subgroups.
- `SplitSolvablePseudoCompleteFixedPointStatement`
  ([`SplitSolvableFixedPointStatement`](../SplitSolvableFixedPointStatement.md)) states the
  fixed-point theorem for split solvable groups acting on pseudo-complete schemes with a
  rational point (CGP Proposition C.1.5), a counterpart of the fixed-point step (16.51) in
  Milne's proof.
- `SmoothMaximalSplitTorusConjugacyStatement`
  ([`Rational.MaximalSplitTorusStatement`](MaximalSplitTorusStatement.md)) states that any two
  maximal split tori of a smooth connected affine group over any field are conjugate by a
  `k`-point. It is proved as `smoothMaximalSplitTorusConjugacy`
  ([`Rational.SmoothMaximalSplitTorusConjugacyProof`](SmoothMaximalSplitTorusConjugacyProof.md)).
