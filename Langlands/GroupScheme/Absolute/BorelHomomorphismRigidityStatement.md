# Statement: homomorphisms agreeing on a Borel subgroup agree

Worker 75.

`Langlands.GroupScheme.BorelHomomorphismRigidityStatement.{u} : Prop` is a statement-only,
`Prop`-valued definition. This module does not prove it, and it adds no other definitions,
theorems or axioms. It imports [`Absolute.Borel`](Borel.md), for `IsBorelSubgroup`, the
base-change functor `GroupScheme.baseChange` and the group-scheme vocabulary over a field.

## Lean statement

```lean
def BorelHomomorphismRigidityStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (G G' : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    [Smooth G'.X.hom] [IsAffineHom G'.X.hom] [ConnectedSpace G'.X.left]
    (B : GroupScheme (Spec (CommRingCat.of k))) (i : B ⟶ G), IsBorelSubgroup i →
    ∀ (R : Type u) [CommRing R] [Algebra k R],
      let b : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of k) :=
        Spec.map (CommRingCat.ofHom (algebraMap k R))
      ∀ (φ₁ φ₂ : (GroupScheme.baseChange b).obj G ⟶ (GroupScheme.baseChange b).obj G'),
        (GroupScheme.baseChange b).map i ≫ φ₁ = (GroupScheme.baseChange b).map i ≫ φ₂ →
          φ₁ = φ₂
```

## Objects and predicates used

- **Group schemes.** `GroupScheme S` is `Grp (Over S)`. For `G : GroupScheme S`, `G.X` is its
  scheme over `S`; `G.X.left` is the underlying scheme and `G.X.hom` its structure morphism.
  Morphisms of `GroupScheme S` are homomorphisms of group schemes over `S`.
- `Smooth`, `IsAffineHom`, `ConnectedSpace`: as in Mathlib; together they say that `G` and
  `G'` are smooth, affine and connected over `k`.
- `IsBorelSubgroup i` ([`Absolute.Borel`](Borel.md)): `i` is a closed immersion, `B` is smooth,
  connected and solvable, and `i` does not factor through a strictly larger smooth connected
  solvable closed subgroup.
- `b : Spec R ⟶ Spec k` is the morphism given by the structure map `k → R`, and
  `GroupScheme.baseChange b` is pullback of group schemes along `b`. So
  `(GroupScheme.baseChange b).obj G` is `G_R`, and `(GroupScheme.baseChange b).map i` is
  `i_R : B_R ⟶ G_R`.

## Statement and quantifiers

For every algebraically closed field `k : Type u`, all smooth, affine, connected group schemes
`G` and `G'` over `Spec k`, every Borel subgroup `i : B ⟶ G`, every commutative `k`-algebra
`R : Type u`, and all homomorphisms `φ₁ φ₂ : G_R ⟶ G'_R` of group schemes over `Spec R`: if
`i_R ≫ φ₁ = i_R ≫ φ₂`, then `φ₁ = φ₂`.

## Source

James S. Milne, *Algebraic Groups: The theory of group schemes of finite type over a field*
(Cambridge University Press, 2017), source ID `milne-2017-algebraic-groups`, file
`Milne--Algebraic groups, the theory of group schemes of finite type over a field
(book)--2017.pdf`. Page numbers are printed page numbers; the PDF page is the printed page
plus 16.

- Proposition 17.21, p.358: "Let G and G′ be connected group varieties over k, let R be a
  k-algebra, and let φ₁, φ₂ : G_R → G′_R be homomorphisms. If φ₁ and φ₂ agree on B_R for some
  Borel subgroup B of G, then they agree on G_R."
- Section 17b, opening, p.353: "In this section, G is a connected group variety over an
  algebraically closed field k."
- Definition 17.6, p.353: a Borel subgroup is a maximal connected solvable subgroup variety.
- Chapter 17 opening, p.352: all algebraic groups are affine over the base field; p.13:
  "group variety" = "smooth algebraic group".

The official errata snapshot of 2026-11-02 (source ID
`milne-2017-algebraic-groups-errata-2026-11-02`) lists Chapter 17 corrections only on pp.360,
364 and 386. None concerns Proposition 17.21.

Milne's proof: the morphism `x ↦ φ₁(x)·φ₂(x)⁻¹` is constant on cosets of `B_R` and so factors
through `(G/B)_R`; as `G/B` is complete and `G'` is affine, it is constant with value `e`.
This is explanation only.

## Derivation from the source

- **Connected group varieties.** As in Section 17b, `k` is algebraically closed, and `G`, `G'`
  are connected group varieties, hence smooth, affine and connected by the Chapter 17
  convention. Both are given these hypotheses, as in the source.
- **`R`-homomorphisms.** `G_R`, `G'_R` and `B_R` are the base changes along `Spec R → Spec k`,
  and `φ₁`, `φ₂` are homomorphisms of group schemes over `R`. "Agree on `B_R`" means equal
  restrictions along `i_R`, and "agree on `G_R`" means `φ₁ = φ₂`.
- **Universe.** The algebra `R` ranges over `Type u`, the universe of `k`.

## Scope

- Milne's following remark (an automorphism of `G_R` that is the identity on `B_R` is the
  identity) is the special case `G' = G`, `φ₂ = 𝟙`, and is not stated separately.

## Related Library results

- [`Absolute.BorelProperQuotientStatement`](BorelProperQuotientStatement.md) states that some
  Borel subgroup has proper homogeneous quotients (part of Milne's Theorem 17.9(a)), the kind
  of completeness of `G/B` used in the proof.
