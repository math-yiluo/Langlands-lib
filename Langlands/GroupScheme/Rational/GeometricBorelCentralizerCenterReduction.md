# The centralizer of a geometric Borel subgroup: reduction to the absolute case

This module reduces Milne's 17.70, stated in the Library as
`GeometricBorelCentralizerCenterStatement`
([`Rational.GeometricBorelCentralizerCenterStatement`](GeometricBorelCentralizerCenterStatement.md)),
to two other Library statements:

- `BorelCentralizerCenterStatement`
  ([`Absolute.BorelCentralizerCenterStatement`](../Absolute/BorelCentralizerCenterStatement.md)),
  Proposition 17.22 over an algebraically closed field: `Z(B) ⊂ C_G(B) = Z(G)`;
- `BorelCenterEqualityStatement`
  ([`Absolute.BorelCenterEqualityStatement`](../Absolute/BorelCenterEqualityStatement.md)),
  Proposition 17.45 for geometric Borel subgroups over an arbitrary field: the points of `Z(G)`
  are exactly the images under `i` of the points of `Z(B)`.

All three statements are imported unchanged. The final theorem is **conditional** on both
statements; this module does not prove `GeometricBorelCentralizerCenterStatement` outright.

## Declarations

### `SubgroupFunctor.baseChange_centralizer_le_centralizer_baseChange`

For an arbitrary morphism of schemes `b : S' ⟶ S`, a group scheme `G` over `S` and a subgroup
functor `F` of `G`:

```lean
F.centralizer.baseChange b ≤ (F.baseChange b).centralizer
```

The base change of the centralizer of `F` lies in the centralizer of the base change of `F`.
Proof: a point of the left side over `T : Over S'` is, through `baseChangePointsEquiv`, a point
of `C_G(F)` over the composite `T ⟶ S' ⟶ S`. Its centralizing property, applied to the test
morphism `(Over.map b).map a` and the point of `F` corresponding to a point `y` of `F.baseChange b`,
gives the commutation in `G` over `S`. Naturality of `baseChangePointsEquiv` and its
multiplicativity transport this commutation back to the base-changed group.

### `centralizer_range_le_center_of_baseChange`

For a faithfully flat quasi-compact morphism `b : S' ⟶ S` (`[QuasiCompact b] [Flat b]
[Surjective b]`), a homomorphism `i : B ⟶ G` of group schemes over `S`, and the hypothesis
`(center G).HasClosedRepresentative` (the centre is represented by a closed subgroup):
if `(SubgroupFunctor.range (i_b)).centralizer ≤ center (G_b)` after base change along `b`, then
`(SubgroupFunctor.range i).centralizer ≤ center G`.

Proof: let `z : Z ⟶ G` be a closed subgroup representing `center G`; its underlying morphism
is a monomorphism. The Library theorem `SubgroupFunctor.le_range_of_baseChange_le` (fpqc base
change reflects containment in a represented subgroup) reduces the claim to
`C_G(B).baseChange b ≤ (range z).baseChange b = (center G).baseChange b`. By
`center_baseChange` the right side is `center (G_b)`. The previous lemma gives
`C_G(B).baseChange b ≤ ((range i).baseChange b).centralizer`, and by
`SubgroupFunctor.range_baseChangeHom` the subgroup `(range i).baseChange b` is `range (i_b)`,
so the hypothesis finishes the proof.

### `geometricBorel_centralizer_range_eq_center`

Assume `BorelCentralizerCenterStatement.{u}`. For every field `k : Type u`, every smooth, affine,
connected group scheme `G` over `Spec k` and every `i : B ⟶ G` with
`IsGeometricBorelSubgroup i`:

```lean
(SubgroupFunctor.range i).centralizer = center G
```

This is point (2) of the target. Proof:

- `center G ≤ C_G(B)` is the Library theorem `SubgroupFunctor.center_le_centralizer`.
- For `C_G(B) ≤ center G`, let `b = toAlgebraicClosure k : Spec k̄ ⟶ Spec k`. It is surjective,
  flat and quasi-compact by `fieldExtension_fpqc k (AlgebraicClosure k)`, and `center G` has a
  closed representative by `center_hasClosedRepresentative` (which needs only that `G` is
  affine over the field). By `centralizer_range_le_center_of_baseChange` it suffices to show
  `C_{G_b}(B_b) ≤ Z(G_b)` over `k̄`. The base change `G_b` is smooth and affine (pullback
  stability) and connected (`GroupScheme.connectedSpace_baseChange_of_smooth_affine`), and the
  second component of `IsGeometricBorelSubgroup i` says exactly that `i_b` is a Borel subgroup
  (`IsBorelSubgroup`). The second conjunct of `BorelCentralizerCenterStatement` at `k̄` gives
  `C_{G_b}(B_b) = Z(G_b)`.

### `GeometricBorelCentralizerCenterReductionStatement`

```lean
def GeometricBorelCentralizerCenterReductionStatement : Prop :=
  BorelCentralizerCenterStatement.{u} → BorelCenterEqualityStatement.{u} →
    GeometricBorelCentralizerCenterStatement.{u}
```

A `Prop`-valued definition: Proposition 17.22 over every algebraically closed field in universe
`u` and Proposition 17.45 over every field in universe `u` together imply Milne 17.70 over every
field in universe `u`. It is an internal reduction statement, not a statement from the source.

### `geometricBorelCentralizerCenterReduction`

The proof of `GeometricBorelCentralizerCenterReductionStatement.{u}`. Point (2) of the target
is `geometricBorel_centralizer_range_eq_center`. For point (1), rewriting `C_G(B)` as
`center G` with point (2) turns it into the conclusion of `BorelCenterEqualityStatement`
applied to the same `k`, `G`, `B`, `i` and geometric Borel hypothesis.

No hypothesis is added to the target beyond the two imported statements. The only use of
Proposition 17.22 is over the algebraic closure of `k`, in its centralizer equality; its first
conjunct `Z(B) ⊂ C_G(B)` is not used.

## Provenance

Derived. Milne gives no separate proof of 17.70: he cites 17.22 and 17.45, and the paragraph
just before 17.70 (Section 17i) reads: "Let G be a connected group variety over k. Because the
formation of centralizers and normalizers commutes with extension of the base field, the
following statements can be deduced from the algebraically closed case." This module implements that deduction
for point (2) by fpqc descent from the algebraic closure, using only the inclusion
`C_G(B)_{k̄} ⊂ C_{G_{k̄}}(B_{k̄})` (the first lemma) and the base-change compatibility of the
centre (`center_baseChange`). Point (1) follows from point (2) and 17.45 as in Milne's citation.

Source: James S. Milne, *Algebraic Groups: The theory of group schemes of finite type over a
field* (Cambridge University Press, 2017), source ID `milne-2017-algebraic-groups`:
17.70 and the preceding paragraph, printed p.376 (one-based PDF p.392); Proposition 17.22,
printed p.359 (PDF p.375); Proposition 17.45, printed p.365 (PDF p.381). The official errata
snapshot `milne-2017-algebraic-groups-errata-2026-11-02` lists Chapter 17 corrections only on
pp.360, 364 and 386, none of which concerns 17.22, 17.45 or 17.70.
